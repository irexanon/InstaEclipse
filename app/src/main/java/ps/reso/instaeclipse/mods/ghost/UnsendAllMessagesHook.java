package ps.reso.instaeclipse.mods.ghost;

import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.AlertDialog;
import android.app.Dialog;
import android.content.Context;
import android.content.ContextWrapper;
import android.content.res.ColorStateList;
import android.content.res.Resources;
import android.graphics.Color;
import android.graphics.Typeface;
import android.graphics.drawable.ColorDrawable;
import android.graphics.drawable.Drawable;
import android.graphics.drawable.GradientDrawable;
import android.graphics.drawable.RippleDrawable;
import android.graphics.drawable.StateListDrawable;
import android.os.Handler;
import android.os.Looper;
import android.os.SystemClock;
import android.util.Base64;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.MotionEvent;
import android.view.View;
import android.view.ViewGroup;
import android.view.Window;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.ProgressBar;
import android.widget.TextView;
import android.widget.Toast;

import org.json.JSONArray;
import org.json.JSONObject;
import org.luckypray.dexkit.DexKitBridge;
import org.luckypray.dexkit.query.FindMethod;
import org.luckypray.dexkit.query.matchers.MethodMatcher;
import org.luckypray.dexkit.result.MethodData;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.lang.ref.WeakReference;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.HttpURLConnection;
import java.net.URI;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.zip.GZIPInputStream;

import de.robv.android.xposed.XC_MethodHook;
import de.robv.android.xposed.XposedBridge;
import de.robv.android.xposed.XposedHelpers;
import ps.reso.instaeclipse.R;
import ps.reso.instaeclipse.mods.ui.UIHookManager;
import ps.reso.instaeclipse.utils.dialog.DialogUtils;
import ps.reso.instaeclipse.utils.feature.FeatureFlags;
import ps.reso.instaeclipse.utils.feature.FeatureStatusTracker;
import ps.reso.instaeclipse.utils.ghost.ThreadNames;
import ps.reso.instaeclipse.utils.i18n.I18n;
import ps.reso.instaeclipse.utils.log.ModuleLog;
import ps.reso.instaeclipse.utils.users.UserUtils;

/**
 * Unsend All Messages in DM Inbox Context Menu:
 *
 * When holding (long-pressing) a user's chat in the Direct inbox, Instagram opens the thread
 * context menu (Pin, Mute, Flag, Delete, etc.). This hook:
 *   1. Captures the target thread's DirectThreadKey, threadId, and display name from the
 *      long-pressed inbox row and DirectThreadStore summaries.
 *   2. Injects a native-styled "Unsend all messages" option into the chat context menu.
 *   3. Shows a confirmation dialog, then a cancellable progress dialog while paginating the
 *      full thread history and unsending all messages sent by the current user ("my side").
 *   4. Removes unsent messages from the local DirectThreadStore cache so the chat updates
 *      immediately without requiring an app restart.
 *
 * Gated on FeatureFlags.unsendAllMessages.
 */
public class UnsendAllMessagesHook {

    private static final String MENU_ITEM_TAG = "ie_unsend_all_menu_row";
    private static final String INBOX_ANCHOR = "DirectThreadStoreImpl.getSortedCopyOfThreadSummaries";
    private static final String[] STORE_ANCHORS = {
            "Posted RemoveThreadEvent with null thread_id for threadKey = ",
            "Entry should exist before function call"
    };
    private static final String DTK_CLASS = "com.instagram.model.direct.DirectThreadKey";
    private static final String USER_SESSION_CLASS = "com.instagram.common.session.UserSession";

    private static final Handler mainHandler = new Handler(Looper.getMainLooper());
    private static final ExecutorService executor = Executors.newSingleThreadExecutor();

    // ── Session & HTTP Header State ──────────────────────────────────────────
    private static final ConcurrentHashMap<String, String> sCapturedHeaders = new ConcurrentHashMap<>();
    private static volatile String sCurrentUserId = null;
    private static volatile Object sUserSession = null;
    private static volatile long sLastHeaderCaptureMs = 0;

    // ── DirectThreadStore & Thread Mapping State ─────────────────────────────
    private static volatile Object sDirectThreadStore = null;
    private static volatile Method sRemoveMethod3 = null;
    private static volatile Method sRemoveMethod4 = null;
    private static final List<Method> sThreadLookupMethods = Collections.synchronizedList(new ArrayList<>());

    private static final Map<String, Object> sThreadKeyById =
            Collections.synchronizedMap(new LinkedHashMap<String, Object>() {
                @Override protected boolean removeEldestEntry(Map.Entry<String, Object> e) { return size() > 400; }
            });
    private static final Map<String, String> sTitleByThreadId =
            Collections.synchronizedMap(new LinkedHashMap<String, String>() {
                @Override protected boolean removeEldestEntry(Map.Entry<String, String> e) { return size() > 400; }
            });
    private static final Map<String, String> sThreadIdByNormalizedTitle =
            Collections.synchronizedMap(new LinkedHashMap<String, String>() {
                @Override protected boolean removeEldestEntry(Map.Entry<String, String> e) { return size() > 800; }
            });

    // ── Last Long-Pressed / Touched Inbox Thread State ───────────────────────
    private static volatile String sSelectedThreadId = null;
    private static volatile Object sSelectedThreadKey = null;
    private static volatile String sSelectedThreadTitle = null;
    private static volatile long sLastInboxInteractionMs = 0;

    private static volatile String sLastStoreLookupThreadId = null;
    private static volatile Object sLastStoreLookupThreadKey = null;
    private static volatile long sLastStoreLookupMs = 0;

    private static volatile WeakReference<Dialog> sLastShownDialog = new WeakReference<>(null);

    // Cached resource IDs
    private static volatile int sInboxRecyclerId = 0;
    private static volatile int sInboxActionBarId = 0;
    private static volatile int sThreadHeaderId = 0;
    private static volatile int sActionSheetContainerId = 0;
    private static volatile int sBottomSheetContainerId = 0;
    private static volatile int sDesignBottomSheetId = 0;

    // Known thread context menu keywords (lowercase) to help identify the chat long-press menu
    private static final String[] THREAD_MENU_KEYWORDS = {
            "delete", "mute", "unmute", "pin", "unpin", "flag", "unflag",
            "mark as unread", "mark as read", "unread", "move to general",
            "move to primary", "leave", "restrict", "hide"
    };

    // ── Install ──────────────────────────────────────────────────────────────

    public void install(DexKitBridge bridge, ClassLoader classLoader) {
        hookInboxSummariesAndStore(bridge, classLoader);
        hookInboxTouchAndLongPress(classLoader);
        hookMenuAttachmentAndDialogs(classLoader);
        FeatureStatusTracker.setHooked("UnsendAllMessages");
        ModuleLog.line("(IE|UnsendAll) ✅ installed");
    }

    // ── 1. Capture Auth Headers & Current User ID from TigonServiceLayer ─────

    /**
     * Called from IGNetworkInterceptor on outgoing Tigon requests. Captures live HTTP headers
     * (Authorization, User-Agent, X-IG-App-ID, Cookie, etc.) and resolves the current user's PK.
     */
    public static void captureSessionFromTigon(Object tigonLayer, Object requestObj, URI uri) {
        try {
            if (uri == null || uri.getHost() == null || !uri.getHost().contains("i.instagram.com")) return;
            long now = SystemClock.uptimeMillis();
            if (sCurrentUserId != null && sCapturedHeaders.containsKey("Authorization")
                    && (now - sLastHeaderCaptureMs) < 45_000L) {
                return;
            }

            if (requestObj != null) {
                extractHeadersFromRequest(requestObj);
            }
            if (tigonLayer != null && (sUserSession == null || sCurrentUserId == null)) {
                extractUserSessionFromObject(tigonLayer);
            }
            if (sCapturedHeaders.containsKey("Authorization") || sCapturedHeaders.containsKey("Cookie")) {
                sLastHeaderCaptureMs = now;
            }
        } catch (Throwable ignored) {}
    }

    private static void extractHeadersFromRequest(Object requestObj) {
        Class<?> cls = requestObj.getClass();
        while (cls != null && cls != Object.class) {
            for (Field f : cls.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers())) continue;
                f.setAccessible(true);
                Object val;
                try { val = f.get(requestObj); } catch (Throwable ignored) { continue; }
                if (val == null) continue;

                if (val instanceof List<?> list && !list.isEmpty()) {
                    inspectHeaderList(list);
                } else if (val instanceof Map<?, ?> map && !map.isEmpty()) {
                    for (Map.Entry<?, ?> entry : map.entrySet()) {
                        if (entry.getKey() instanceof String k && entry.getValue() instanceof String v) {
                            recordHeader(k, v);
                        }
                    }
                }
            }
            cls = cls.getSuperclass();
        }
    }

    private static void inspectHeaderList(List<?> list) {
        Field firstStrField = null;
        Field secondStrField = null;

        for (Object elem : list) {
            if (elem == null) continue;
            if (firstStrField == null || secondStrField == null) {
                List<Field> strFields = new ArrayList<>(2);
                for (Class<?> c = elem.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
                    for (Field f : c.getDeclaredFields()) {
                        if (!Modifier.isStatic(f.getModifiers()) && f.getType() == String.class) {
                            f.setAccessible(true);
                            strFields.add(f);
                        }
                    }
                }
                if (strFields.size() < 2) return;
                firstStrField = strFields.get(0);
                secondStrField = strFields.get(1);
            }

            try {
                String s1 = (String) firstStrField.get(elem);
                String s2 = (String) secondStrField.get(elem);
                if (s1 == null || s2 == null) continue;
                if (looksLikeHeaderName(s1)) {
                    recordHeader(s1, s2);
                } else if (looksLikeHeaderName(s2)) {
                    recordHeader(s2, s1);
                }
            } catch (Throwable ignored) {}
        }
    }

    private static boolean looksLikeHeaderName(String s) {
        if (s == null || s.isEmpty() || s.length() > 45) return false;
        if (s.contains(" ") || s.contains("/") || s.contains(";") || s.contains(":")) return false;
        String lower = s.toLowerCase(Locale.US);
        return lower.equals("authorization")
                || lower.equals("user-agent")
                || lower.equals("cookie")
                || lower.equals("accept-language")
                || lower.startsWith("x-ig-")
                || lower.startsWith("ig-u-")
                || lower.equals("x-mid")
                || lower.equals("x-fb-http-engine")
                || lower.equals("x-bloks-version-id");
    }

    private static void recordHeader(String rawKey, String value) {
        if (rawKey == null || value == null || value.isEmpty()) return;
        String key = rawKey.trim();
        String lower = key.toLowerCase(Locale.US);
        if (lower.equals("accept-encoding") || lower.equals("content-length")
                || lower.equals("content-type") || lower.equals("host")) {
            return;
        }
        if (lower.equals("authorization")) {
            sCapturedHeaders.put("Authorization", value);
            String uid = parseUserIdFromBearer(value);
            if (uid != null) sCurrentUserId = uid;
        } else if (lower.equals("user-agent")) {
            sCapturedHeaders.put("User-Agent", value);
        } else if (lower.equals("cookie")) {
            sCapturedHeaders.put("Cookie", value);
            String uid = parseUserIdFromCookie(value);
            if (uid != null) sCurrentUserId = uid;
        } else if (lower.equals("ig-u-ds-user-id")) {
            sCapturedHeaders.put("IG-U-DS-USER-ID", value);
            if (isNumericId(value)) sCurrentUserId = value.trim();
        } else {
            sCapturedHeaders.put(key, value);
        }
    }

    private static String parseUserIdFromBearer(String auth) {
        try {
            int idx = auth.indexOf("IGT:2:");
            if (idx < 0) return null;
            String b64 = auth.substring(idx + 6).trim();
            byte[] decoded = Base64.decode(b64, Base64.DEFAULT);
            JSONObject obj = new JSONObject(new String(decoded, StandardCharsets.UTF_8));
            String uid = obj.optString("ds_user_id", "");
            if (isNumericId(uid)) return uid;
        } catch (Throwable ignored) {}
        return null;
    }

    private static String parseUserIdFromCookie(String cookie) {
        try {
            for (String part : cookie.split(";")) {
                String trimmed = part.trim();
                if (trimmed.startsWith("ds_user_id=")) {
                    String uid = trimmed.substring("ds_user_id=".length()).trim();
                    if (isNumericId(uid)) return uid;
                }
            }
        } catch (Throwable ignored) {}
        return null;
    }

    private static void extractUserSessionFromObject(Object owner) {
        if (owner == null) return;
        for (Class<?> c = owner.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
            for (Field f : c.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers())) continue;
                if (!USER_SESSION_CLASS.equals(f.getType().getName())) continue;
                try {
                    f.setAccessible(true);
                    Object session = f.get(owner);
                    if (session != null) {
                        sUserSession = session;
                        String uid = extractUserIdFromSession(session);
                        if (uid != null) sCurrentUserId = uid;
                        return;
                    }
                } catch (Throwable ignored) {}
            }
        }
    }

    private static String extractUserIdFromSession(Object session) {
        if (session == null) return null;
        try {
            Method m = session.getClass().getMethod("getUserId");
            Object r = m.invoke(session);
            if (r instanceof String s && isNumericId(s)) return s;
        } catch (Throwable ignored) {}

        for (Class<?> c = session.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
            for (Field f : c.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers()) || f.getType() != String.class) continue;
                try {
                    f.setAccessible(true);
                    String s = (String) f.get(session);
                    if (s == null) continue;
                    if (isNumericId(s)) return s;
                    if (s.contains(":")) {
                        String prefix = s.substring(0, s.indexOf(':'));
                        if (isNumericId(prefix)) return prefix;
                    }
                } catch (Throwable ignored) {}
            }
        }
        return null;
    }

    private static boolean isNumericId(String s) {
        if (s == null || s.length() < 4 || s.length() > 25) return false;
        for (int i = 0; i < s.length(); i++) {
            if (!Character.isDigit(s.charAt(i))) return false;
        }
        return true;
    }

    // ── 2. DirectThreadStore & Inbox Summary Tracking ────────────────────────

    private void hookInboxSummariesAndStore(DexKitBridge bridge, ClassLoader classLoader) {
        XC_MethodHook summaryHook = new XC_MethodHook() {
            @Override
            protected void afterHookedMethod(MethodHookParam param) {
                try {
                    if (param.thisObject != null) {
                        sDirectThreadStore = param.thisObject;
                        if (sUserSession == null || sCurrentUserId == null) {
                            extractUserSessionFromObject(param.thisObject);
                        }
                    }
                    Object result = param.getResult();
                    if (!(result instanceof List<?> list) || list.isEmpty()) return;
                    for (Object row : list) {
                        indexThreadSummaryRow(row);
                    }
                } catch (Throwable ignored) {}
            }
        };

        try {
            Set<Class<?>> storeClasses = new LinkedHashSet<>();
            for (MethodData md : bridge.findMethod(FindMethod.create()
                    .matcher(MethodMatcher.create().usingStrings(INBOX_ANCHOR)))) {
                try {
                    Method m = md.getMethodInstance(classLoader);
                    m.setAccessible(true);
                    XposedBridge.hookMethod(m, summaryHook);
                    storeClasses.add(m.getDeclaringClass());
                } catch (Throwable ignored) {}
            }

            for (String anchor : STORE_ANCHORS) {
                for (MethodData md : bridge.findMethod(FindMethod.create()
                        .matcher(MethodMatcher.create().usingStrings(anchor)))) {
                    try {
                        storeClasses.add(md.getMethodInstance(classLoader).getDeclaringClass());
                    } catch (Throwable ignored) {}
                }
            }

            // On DirectThreadStoreImpl, resolve local remove methods and thread lookup methods
            XC_MethodHook lookupTracker = new XC_MethodHook() {
                @Override
                protected void beforeHookedMethod(MethodHookParam param) {
                    if (Looper.myLooper() != Looper.getMainLooper()) return;
                    if (param.thisObject != null) sDirectThreadStore = param.thisObject;
                    if (param.args != null && param.args.length > 0 && param.args[0] != null
                            && param.args[0].getClass().getName().equals(DTK_CLASS)) {
                        String tid = extractThreadIdFromKey(param.args[0]);
                        if (tid != null) {
                            sLastStoreLookupThreadKey = param.args[0];
                            sLastStoreLookupThreadId = tid;
                            sLastStoreLookupMs = SystemClock.uptimeMillis();
                            sThreadKeyById.put(tid, param.args[0]);
                        }
                    }
                }
            };

            for (Class<?> storeCls : storeClasses) {
                for (Method m : storeCls.getDeclaredMethods()) {
                    Class<?>[] p = m.getParameterTypes();
                    if (m.getReturnType() == void.class && Modifier.isSynchronized(m.getModifiers())) {
                        if (p.length == 3 && p[0].getName().equals(DTK_CLASS)
                                && p[1] == String.class && p[2] == String.class) {
                            m.setAccessible(true);
                            sRemoveMethod3 = m;
                        } else if (p.length == 4 && p[0].getName().equals(DTK_CLASS)
                                && p[1] == String.class && p[2] == String.class && p[3] == boolean.class) {
                            m.setAccessible(true);
                            sRemoveMethod4 = m;
                        }
                    } else if (p.length == 1 && p[0].getName().equals(DTK_CLASS)
                            && m.getReturnType() != void.class && !m.getReturnType().isPrimitive()) {
                        try {
                            m.setAccessible(true);
                            sThreadLookupMethods.add(m);
                            XposedBridge.hookMethod(m, lookupTracker);
                        } catch (Throwable ignored) {}
                    }
                }
            }
        } catch (Throwable t) {
            ModuleLog.line("(IE|UnsendAll) ⚠️ store hooks: " + t.getMessage());
        }
    }

    private static void indexThreadSummaryRow(Object row) {
        if (row == null) return;
        Object dtk = findDirectThreadKey(row, 0, Collections.newSetFromMap(new IdentityHashMap<>()), 2);
        String threadId = extractThreadIdFromKey(dtk);
        if (threadId == null) return;
        sThreadKeyById.put(threadId, dtk);

        // Extract candidate titles and participant usernames from the summary row
        List<String> titles = new ArrayList<>();
        for (Class<?> c = row.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
            for (Field f : c.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers())) continue;
                f.setAccessible(true);
                Object v;
                try { v = f.get(row); } catch (Throwable ignored) { continue; }
                if (v instanceof String s) {
                    if (looksLikeDisplayName(s, threadId)) titles.add(s.trim());
                } else if (v instanceof List<?> list && list.size() <= 30) {
                    for (Object item : list) {
                        if (item == null) continue;
                        String uname = UserUtils.callUsernameGetter(item);
                        if (uname != null && !uname.isEmpty()) titles.add(uname);
                        for (Field uf : item.getClass().getDeclaredFields()) {
                            if (!Modifier.isStatic(uf.getModifiers()) && uf.getType() == String.class) {
                                try {
                                    uf.setAccessible(true);
                                    String us = (String) uf.get(item);
                                    if (looksLikeDisplayName(us, threadId)) titles.add(us.trim());
                                } catch (Throwable ignored) {}
                            }
                        }
                    }
                }
            }
        }

        for (String t : titles) {
            String norm = normalizeTitle(t);
            if (!norm.isEmpty()) {
                sThreadIdByNormalizedTitle.put(norm, threadId);
                if (!sTitleByThreadId.containsKey(threadId)) {
                    sTitleByThreadId.put(threadId, t);
                }
            }
        }
    }

    private static boolean looksLikeDisplayName(String s, String threadId) {
        if (s == null) return false;
        String t = s.trim();
        if (t.length() < 2 || t.length() > 60) return false;
        if (t.equals(threadId)) return false;
        if (t.startsWith("http") || t.startsWith("mid.") || t.startsWith("{")) return false;
        if (t.chars().allMatch(Character::isDigit)) return false;
        if (t.equals(t.toUpperCase(Locale.US)) && t.contains("_")) return false; // enum constants
        return true;
    }

    private static String normalizeTitle(String s) {
        return s == null ? "" : s.trim().toLowerCase(Locale.ROOT);
    }

    // ── 3. Inbox Row Touch & Long-Press Tracking ─────────────────────────────

    private void hookInboxTouchAndLongPress(ClassLoader classLoader) {
        // Hook Activity.dispatchTouchEvent so every touch-down in any Activity is captured using
        // screen coordinates, even when obfuscated RecyclerView subclasses override dispatchTouchEvent
        // or use GestureDetector for long-presses.
        try {
            XposedHelpers.findAndHookMethod(Activity.class, "dispatchTouchEvent", MotionEvent.class,
                    new XC_MethodHook() {
                        @Override
                        protected void beforeHookedMethod(MethodHookParam param) {
                            if (!FeatureFlags.unsendAllMessages) return;
                            if (!(param.args[0] instanceof MotionEvent ev)) return;
                            int action = ev.getActionMasked();
                            if (action != MotionEvent.ACTION_DOWN) return;

                            Activity act = (Activity) param.thisObject;
                            watchActivity(act);
                            ensureResourceIds(act);

                            Window w = act.getWindow();
                            if (w == null) return;
                            View decor = w.getDecorView();
                            if (!(decor instanceof ViewGroup decorGroup)) return;

                            float rawX = ev.getRawX();
                            float rawY = ev.getRawY();

                            List<ViewGroup> rvs = new ArrayList<>();
                            findCandidateRecyclerViewsUnder(decorGroup, rawX, rawY, rvs);
                            for (ViewGroup rv : rvs) {
                                View rowView = findDirectChildAtScreenPos(rv, rawX, rawY);
                                if (rowView != null) {
                                    sLastInboxInteractionMs = SystemClock.uptimeMillis();
                                    captureThreadFromInboxRow(rv, rowView);
                                    break;
                                }
                            }
                        }
                    });
        } catch (Throwable t) {
            ModuleLog.line("(IE|UnsendAll) ⚠️ Activity.dispatchTouchEvent hook: " + t.getMessage());
        }

        // Hook GestureDetector.SimpleOnGestureListener.onLongPress to trigger menu sweeps when
        // Instagram's RecyclerView item touch listener detects a long-press.
        try {
            XposedHelpers.findAndHookMethod(
                    android.view.GestureDetector.SimpleOnGestureListener.class,
                    "onLongPress", MotionEvent.class,
                    new XC_MethodHook() {
                        @Override
                        protected void afterHookedMethod(MethodHookParam param) {
                            if (!FeatureFlags.unsendAllMessages) return;
                            sLastInboxInteractionMs = SystemClock.uptimeMillis();
                            scheduleAllWindowsSweep();
                        }
                    });
        } catch (Throwable ignored) {}

        // Also hook View.performLongClick() as a direct trigger when a row fires standard long-click
        try {
            XposedHelpers.findAndHookMethod(View.class, "performLongClick", new XC_MethodHook() {
                @Override
                protected void beforeHookedMethod(MethodHookParam param) {
                    if (!FeatureFlags.unsendAllMessages) return;
                    View v = (View) param.thisObject;
                    ensureResourceIds(v.getContext());
                    sLastInboxInteractionMs = SystemClock.uptimeMillis();
                    ViewGroup rvGroup = findEnclosingRecyclerView(v);
                    if (rvGroup != null && !isInsideSheetContainer(rvGroup, rvGroup.getRootView(), false)) {
                        View rowView = v;
                        while (rowView.getParent() != rvGroup && rowView.getParent() instanceof View p) {
                            rowView = p;
                        }
                        captureThreadFromInboxRow(rvGroup, rowView);
                    }
                    scheduleAllWindowsSweep();
                }
            });
        } catch (Throwable ignored) {}
    }

    private static void findCandidateRecyclerViewsUnder(ViewGroup root, float rawX, float rawY, List<ViewGroup> out) {
        if (root == null || root.getVisibility() != View.VISIBLE) return;
        int id = root.getId();
        if ((sActionSheetContainerId != 0 && id == sActionSheetContainerId)
                || (sBottomSheetContainerId != 0 && id == sBottomSheetContainerId)
                || (sDesignBottomSheetId != 0 && id == sDesignBottomSheetId)) {
            return; // skip bottom sheet containers when looking for the inbox list
        }
        if ((sInboxRecyclerId != 0 && id == sInboxRecyclerId) || isRecyclerViewOrListView(root)) {
            if (containsScreenPoint(root, rawX, rawY) && root.getChildCount() > 0) {
                if (sInboxRecyclerId != 0 && id == sInboxRecyclerId) {
                    out.add(0, root); // prioritize exact inbox RecyclerView ID
                } else {
                    out.add(root);
                }
            }
        }
        for (int i = 0; i < root.getChildCount(); i++) {
            View c = root.getChildAt(i);
            if (c instanceof ViewGroup vg && c.getVisibility() == View.VISIBLE) {
                findCandidateRecyclerViewsUnder(vg, rawX, rawY, out);
            }
        }
    }

    private static View findDirectChildAtScreenPos(ViewGroup parent, float rawX, float rawY) {
        for (int i = parent.getChildCount() - 1; i >= 0; i--) {
            View child = parent.getChildAt(i);
            if (child == null || child.getVisibility() != View.VISIBLE) continue;
            if (containsScreenPoint(child, rawX, rawY)) {
                return child;
            }
        }
        return null;
    }

    private static boolean containsScreenPoint(View v, float rawX, float rawY) {
        if (v == null || !v.isShown() || v.getWidth() <= 0 || v.getHeight() <= 0) return false;
        int[] loc = new int[2];
        v.getLocationOnScreen(loc);
        return rawX >= loc[0] && rawX <= (loc[0] + v.getWidth())
                && rawY >= loc[1] && rawY <= (loc[1] + v.getHeight());
    }

    private static ViewGroup findEnclosingRecyclerView(View v) {
        for (android.view.ViewParent p = v.getParent(); p instanceof ViewGroup vg; p = vg.getParent()) {
            if ((sInboxRecyclerId != 0 && vg.getId() == sInboxRecyclerId) || isRecyclerViewOrListView(vg)) {
                return vg;
            }
        }
        return null;
    }

    private static void captureThreadFromInboxRow(ViewGroup recyclerView, View rowView) {
        try {
            Object foundKey = null;
            String foundId = null;

            // Strategy A: Inspect RecyclerView.ViewHolder for this rowView
            try {
                Method getVh = recyclerView.getClass().getMethod("getChildViewHolder", View.class);
                Object vh = getVh.invoke(recyclerView, rowView);
                if (vh != null) {
                    foundKey = findDirectThreadKey(vh, 0, Collections.newSetFromMap(new IdentityHashMap<>()), 6);
                    if (foundKey != null) {
                        foundId = extractThreadIdFromKey(foundKey);
                    } else {
                        foundId = findKnownThreadIdInGraph(vh, 0, Collections.newSetFromMap(new IdentityHashMap<>()), 6);
                    }
                }
            } catch (Throwable ignored) {}

            // Strategy B: Inspect RecyclerView.Adapter item at row's adapter position
            if (foundId == null) {
                try {
                    int pos = -1;
                    try {
                        pos = (int) recyclerView.getClass()
                                .getMethod("getChildAdapterPosition", View.class)
                                .invoke(recyclerView, rowView);
                    } catch (Throwable ignored) {}
                    if (pos >= 0) {
                        Object adapter = recyclerView.getClass().getMethod("getAdapter").invoke(recyclerView);
                        if (adapter != null) {
                            Object item = getAdapterItemAt(adapter, pos);
                            if (item != null) {
                                foundKey = findDirectThreadKey(item, 0, Collections.newSetFromMap(new IdentityHashMap<>()), 6);
                                if (foundKey != null) {
                                    foundId = extractThreadIdFromKey(foundKey);
                                } else {
                                    foundId = findKnownThreadIdInGraph(item, 0, Collections.newSetFromMap(new IdentityHashMap<>()), 6);
                                }
                            }
                        }
                    }
                } catch (Throwable ignored) {}
            }

            // Strategy C: Scan rowView itself (tags & fields)
            if (foundId == null) {
                foundKey = findDirectThreadKey(rowView, 0, Collections.newSetFromMap(new IdentityHashMap<>()), 5);
                if (foundKey != null) {
                    foundId = extractThreadIdFromKey(foundKey);
                } else {
                    foundId = findKnownThreadIdInGraph(rowView, 0, Collections.newSetFromMap(new IdentityHashMap<>()), 5);
                }
            }

            // Extract visible title from rowView for display & title-matching fallback
            List<String> rowTexts = new ArrayList<>();
            collectVisibleTexts(rowView, rowTexts, 12);
            String rowTitle = !rowTexts.isEmpty() ? rowTexts.get(0) : null;

            // Strategy D: Match row texts against indexed thread summaries
            if (foundId == null && !rowTexts.isEmpty()) {
                for (String txt : rowTexts) {
                    String tid = sThreadIdByNormalizedTitle.get(normalizeTitle(txt));
                    if (tid != null) {
                        foundId = tid;
                        rowTitle = txt;
                        break;
                    }
                }
            }

            if (foundId != null) {
                sSelectedThreadId = foundId;
                sSelectedThreadKey = foundKey != null ? foundKey : sThreadKeyById.get(foundId);
                if (rowTitle != null && !rowTitle.isEmpty()) {
                    sSelectedThreadTitle = rowTitle;
                    sTitleByThreadId.put(foundId, rowTitle);
                    ThreadNames.put(foundId, rowTitle);
                } else {
                    sSelectedThreadTitle = sTitleByThreadId.get(foundId);
                }
                ModuleLog.line("(IE|UnsendAll) captured inbox row threadId=" + foundId
                        + " title=" + sSelectedThreadTitle);
            } else if (rowTitle != null) {
                sSelectedThreadTitle = rowTitle;
            }
        } catch (Throwable ignored) {}
    }

    private static Object getAdapterItemAt(Object adapter, int pos) {
        if (adapter == null || pos < 0) return null;
        try {
            Method m = adapter.getClass().getMethod("getItem", int.class);
            m.setAccessible(true);
            Object item = m.invoke(adapter, pos);
            if (item != null) return item;
        } catch (Throwable ignored) {}

        // Scan adapter fields (and nested differ/list holders) for a List whose size > pos
        for (Class<?> c = adapter.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
            for (Field f : c.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers())) continue;
                f.setAccessible(true);
                Object v;
                try { v = f.get(adapter); } catch (Throwable ignored) { continue; }
                if (v instanceof List<?> list && pos < list.size()) {
                    Object elem = list.get(pos);
                    if (elem != null && !(elem instanceof View)) return elem;
                } else if (v != null && !f.getType().isPrimitive()
                        && (v.getClass().getName().startsWith("X.")
                        || v.getClass().getName().startsWith("com.instagram.")
                        || v.getClass().getName().startsWith("androidx.recyclerview."))) {
                    for (Field nf : v.getClass().getDeclaredFields()) {
                        if (Modifier.isStatic(nf.getModifiers())) continue;
                        if (List.class.isAssignableFrom(nf.getType())) {
                            try {
                                nf.setAccessible(true);
                                Object nl = nf.get(v);
                                if (nl instanceof List<?> list && pos < list.size()) {
                                    Object elem = list.get(pos);
                                    if (elem != null && !(elem instanceof View)) return elem;
                                }
                            } catch (Throwable ignored) {}
                        }
                    }
                }
            }
        }
        return null;
    }

    // ── 4. Context Menu Detection & Row Injection ────────────────────────────

    /**
     * Called from UIHookManager.setupHooks(activity) and Activity.onResume to register a persistent
     * global layout listener on the Activity's decor view, matching RemoveMetaAIHook.watchActionSheet.
     */
    public static void watchActivity(final Activity activity) {
        if (activity == null) return;
        try {
            Window w = activity.getWindow();
            if (w == null) return;
            View decor = w.getDecorView();
            watchDecorView(decor, false);
        } catch (Throwable ignored) {}
    }

    private static void watchDecorView(final View decor, final boolean isDialogRoot) {
        if (decor == null) return;
        if (Boolean.TRUE.equals(sWatchedDecorViews.get(decor))) return;
        sWatchedDecorViews.put(decor, Boolean.TRUE);
        try {
            decor.getViewTreeObserver().addOnGlobalLayoutListener(() -> {
                if (!FeatureFlags.unsendAllMessages) return;
                tryInjectIntoMenu(decor, isDialogRoot);
                sweepWindowManagerRoots();
            });
        } catch (Throwable ignored) {}
    }

    private void hookMenuAttachmentAndDialogs(ClassLoader classLoader) {
        // Watch all resumed Activities automatically
        try {
            XposedHelpers.findAndHookMethod(Activity.class, "onResume", new XC_MethodHook() {
                @Override
                protected void afterHookedMethod(MethodHookParam param) {
                    if (param.thisObject instanceof Activity act) {
                        watchActivity(act);
                    }
                }
            });
        } catch (Throwable ignored) {}

        // Track shown Dialogs so we can inspect Dialog-hosted context menus and dismiss them cleanly
        try {
            XposedHelpers.findAndHookMethod(Dialog.class, "show", new XC_MethodHook() {
                @Override
                protected void afterHookedMethod(MethodHookParam param) {
                    if (!FeatureFlags.unsendAllMessages) return;
                    Dialog d = (Dialog) param.thisObject;
                    sLastShownDialog = new WeakReference<>(d);
                    Window w = d.getWindow();
                    if (w != null) {
                        View decor = w.getDecorView();
                        watchDecorView(decor, true);
                        scheduleMenuCheck(decor, true);
                    }
                    scheduleAllWindowsSweep();
                }
            });
        } catch (Throwable ignored) {}

        // Also hook PopupWindow in case Instagram displays context options in a PopupWindow
        try {
            XC_MethodHook popupHook = new XC_MethodHook() {
                @Override
                protected void afterHookedMethod(MethodHookParam param) {
                    if (!FeatureFlags.unsendAllMessages) return;
                    if (param.thisObject instanceof android.widget.PopupWindow pw) {
                        View cv = pw.getContentView();
                        if (cv != null) {
                            View root = cv.getRootView();
                            watchDecorView(root, true);
                            scheduleMenuCheck(root, true);
                        }
                    }
                    scheduleAllWindowsSweep();
                }
            };
            XposedBridge.hookAllMethods(android.widget.PopupWindow.class, "showAtLocation", popupHook);
            XposedBridge.hookAllMethods(android.widget.PopupWindow.class, "showAsDropDown", popupHook);
        } catch (Throwable ignored) {}

        // Hook View.onAttachedToWindow to catch bottom sheets / action sheets added inside the Activity
        // or inside a BottomSheetDialog
        try {
            XposedHelpers.findAndHookMethod(View.class, "onAttachedToWindow", new XC_MethodHook() {
                @Override
                protected void afterHookedMethod(MethodHookParam param) {
                    if (!FeatureFlags.unsendAllMessages) return;
                    View v = (View) param.thisObject;
                    if (!(v instanceof ViewGroup)) return;
                    ensureResourceIds(v.getContext());
                    int id = v.getId();
                    if ((sActionSheetContainerId != 0 && id == sActionSheetContainerId)
                            || (sBottomSheetContainerId != 0 && id == sBottomSheetContainerId)
                            || (sDesignBottomSheetId != 0 && id == sDesignBottomSheetId)
                            || (SystemClock.uptimeMillis() - sLastInboxInteractionMs < 6000L)) {
                        View root = v.getRootView();
                        watchDecorView(root, false);
                        scheduleMenuCheck(root, false);
                    }
                }
            });
        } catch (Throwable t) {
            ModuleLog.line("(IE|UnsendAll) ⚠️ onAttachedToWindow hook: " + t.getMessage());
        }
    }

    private static final Set<View> sPendingRoots = Collections.newSetFromMap(new IdentityHashMap<>());

    private static void scheduleMenuCheck(final View root, final boolean isDialogRoot) {
        if (root == null) return;
        if (!sPendingRoots.add(root)) return;
        mainHandler.postDelayed(() -> {
            sPendingRoots.remove(root);
            tryInjectIntoMenu(root, isDialogRoot);
        }, 45);
        mainHandler.postDelayed(() -> tryInjectIntoMenu(root, isDialogRoot), 150);
        mainHandler.postDelayed(() -> tryInjectIntoMenu(root, isDialogRoot), 320);
    }

    private static void scheduleAllWindowsSweep() {
        mainHandler.postDelayed(UnsendAllMessagesHook::sweepAllWindows, 45);
        mainHandler.postDelayed(UnsendAllMessagesHook::sweepAllWindows, 140);
        mainHandler.postDelayed(UnsendAllMessagesHook::sweepAllWindows, 300);
        mainHandler.postDelayed(UnsendAllMessagesHook::sweepAllWindows, 550);
    }

    private static void sweepAllWindows() {
        if (!FeatureFlags.unsendAllMessages) return;
        try {
            Activity act = UIHookManager.getCurrentActivity();
            if (act != null && act.getWindow() != null) {
                tryInjectIntoMenu(act.getWindow().getDecorView(), false);
            }
            Dialog d = sLastShownDialog.get();
            if (d != null && d.isShowing() && d.getWindow() != null) {
                tryInjectIntoMenu(d.getWindow().getDecorView(), true);
            }
            sweepWindowManagerRoots();
        } catch (Throwable ignored) {}
    }

    @SuppressLint("PrivateApi")
    private static void sweepWindowManagerRoots() {
        try {
            Class<?> wmgClass = Class.forName("android.view.WindowManagerGlobal");
            Object wmg = wmgClass.getMethod("getInstance").invoke(null);
            Field viewsField = wmgClass.getDeclaredField("mViews");
            viewsField.setAccessible(true);
            Object viewsObj = viewsField.get(wmg);
            if (viewsObj instanceof List<?> views) {
                for (int i = views.size() - 1; i >= 0; i--) {
                    Object item = views.get(i);
                    if (item instanceof View rootView && rootView.getVisibility() == View.VISIBLE) {
                        watchDecorView(rootView, true);
                        tryInjectIntoMenu(rootView, true);
                    }
                }
            }
        } catch (Throwable ignored) {}
    }

    private static void tryInjectIntoMenu(View root, boolean isDialogRoot) {
        if (!FeatureFlags.unsendAllMessages || !(root instanceof ViewGroup rootGroup)) return;
        if (root.getVisibility() != View.VISIBLE) return;
        try {
            if (root.findViewWithTag(MENU_ITEM_TAG) != null) return; // already injected

            Context ctx = root.getContext();
            ensureResourceIds(ctx);

            boolean recentInboxTouch = (SystemClock.uptimeMillis() - sLastInboxInteractionMs) < 8000L;

            // Find the ViewGroup holding the option rows (Pin, Mute, Flag, Delete, etc.) across rootGroup.
            // Note: we do NOT short-circuit on root.findViewById(sActionSheetContainerId) because an
            // Activity decorView can contain an old/hidden action_sheet_container while the active sheet
            // is in bottom_sheet_container, design_bottom_sheet, or another child ViewGroup.
            MenuTarget target = findMenuTarget(rootGroup, recentInboxTouch, isDialogRoot);
            if (target == null || target.sampleRow == null) return;

            final ViewGroup menuContainer = target.rowListGroup;
            if (menuContainer.findViewWithTag(MENU_ITEM_TAG) != null) return;

            // Resolve the target threadId and title before injecting
            final String threadId = resolveTargetThreadId(rootGroup);
            final Object threadKey = threadId != null ? sThreadKeyById.get(threadId) : sSelectedThreadKey;
            final String threadTitle = resolveTargetThreadTitle(threadId, rootGroup);

            View unsendRow = buildUnsendMenuRow(menuContainer.getContext(), target.sampleRow, v -> {
                dismissMenu(root);
                final Activity hostAct = UIHookManager.getCurrentActivity() != null
                        ? UIHookManager.getCurrentActivity()
                        : activityFromContext(menuContainer.getContext());
                final Context dialogCtx = hostAct != null ? hostAct : menuContainer.getContext();
                mainHandler.postDelayed(() -> {
                    String resolvedId = threadId != null ? threadId : resolveTargetThreadId(null);
                    Object resolvedKey = threadKey != null ? threadKey
                            : (resolvedId != null ? sThreadKeyById.get(resolvedId) : sSelectedThreadKey);
                    String resolvedTitle = (threadTitle != null && !threadTitle.isEmpty())
                            ? threadTitle
                            : (resolvedId != null ? sTitleByThreadId.get(resolvedId) : null);
                    showConfirmationDialog(dialogCtx, resolvedId, resolvedKey, resolvedTitle);
                }, 160);
            });

            insertRowIntoTarget(target, unsendRow, rootGroup);
            ModuleLog.line("(IE|UnsendAll) ✅ injected menu option into "
                    + menuContainer.getClass().getSimpleName()
                    + " for threadId=" + threadId + " title=" + threadTitle);
        } catch (Throwable t) {
            ModuleLog.line("(IE|UnsendAll) ⚠️ tryInjectIntoMenu: " + t.getMessage());
        }
    }

    private static final class MenuTarget {
        final ViewGroup rowListGroup;
        final View sampleRow;
        final View deleteRow;

        MenuTarget(ViewGroup rowListGroup, View sampleRow, View deleteRow) {
            this.rowListGroup = rowListGroup;
            this.sampleRow = sampleRow;
            this.deleteRow = deleteRow;
        }
    }

    /**
     * Scans the window / sheet subtree for the ViewGroup whose children are the thread context menu
     * option rows (e.g. Pin, Mute, Delete, Flag, Mark as unread). Never touches the inbox RecyclerView.
     */
    private static MenuTarget findMenuTarget(ViewGroup rootGroup, boolean recentInboxTouch, boolean isDialogRoot) {
        ArrayDeque<ViewGroup> queue = new ArrayDeque<>();
        queue.add(rootGroup);

        ViewGroup bestContainer = null;
        View bestSampleRow = null;
        View bestDeleteRow = null;
        int bestScore = 0;

        while (!queue.isEmpty()) {
            ViewGroup vg = queue.poll();
            if (vg == null || vg.getVisibility() != View.VISIBLE || !vg.isShown()) continue;
            if (sInboxRecyclerId != 0 && vg.getId() == sInboxRecyclerId) continue;

            boolean inSheet = isInsideSheetContainer(vg, rootGroup, isDialogRoot);
            boolean isRvOrList = isRecyclerViewOrListView(vg);

            int childCount = vg.getChildCount();
            // Skip huge lists outside sheets (e.g., feed or inbox RecyclerView)
            if (!inSheet && isRvOrList && childCount > 14) {
                continue;
            }

            if (childCount >= 2 && childCount <= 20) {
                int optionRowCount = 0;
                int keywordHits = 0;
                View firstOptionRow = null;
                View deleteRow = null;
                boolean isOwnDialog = false;

                for (int i = 0; i < childCount; i++) {
                    View child = vg.getChildAt(i);
                    if (child == null || child.getVisibility() != View.VISIBLE) continue;
                    if (MENU_ITEM_TAG.equals(child.getTag())) return null; // already has our row

                    List<String> rowTexts = new ArrayList<>(4);
                    collectVisibleTexts(child, rowTexts, 4);
                    if (rowTexts.isEmpty()) continue;

                    for (String rt : rowTexts) {
                        if (rt.startsWith("InstaEclipse")
                                || rt.equals("Unsend All Messages?")
                                || rt.startsWith("Unsending Messages")) {
                            isOwnDialog = true;
                            break;
                        }
                    }
                    if (isOwnDialog) break;

                    boolean matchedKeyword = false;
                    for (String rt : rowTexts) {
                        String lower = rt.toLowerCase(Locale.ROOT);
                        for (String kw : THREAD_MENU_KEYWORDS) {
                            if (lower.equals(kw)
                                    || lower.startsWith(kw + " ")
                                    || lower.endsWith(" " + kw)
                                    || lower.contains(" " + kw + " ")) {
                                matchedKeyword = true;
                                if (lower.contains("delete") || lower.contains("leave")) {
                                    deleteRow = child;
                                }
                                break;
                            }
                        }
                        if (matchedKeyword) break;
                    }

                    boolean interactiveRow = matchedKeyword || isRvOrList || isInteractive(child);
                    if (!interactiveRow) continue;

                    optionRowCount++;
                    if (firstOptionRow == null) firstOptionRow = child;
                    if (matchedKeyword) keywordHits++;
                }

                if (!isOwnDialog && optionRowCount >= 2 && optionRowCount <= 15) {
                    boolean qualifies = (keywordHits >= 2)
                            || (keywordHits >= 1 && (inSheet || recentInboxTouch))
                            || (inSheet && recentInboxTouch && optionRowCount >= 3 && optionRowCount <= 10);
                    if (qualifies) {
                        int score = keywordHits * 15 + (inSheet ? 20 : 0) + optionRowCount;
                        if (score > bestScore) {
                            bestScore = score;
                            bestContainer = vg;
                            bestSampleRow = deleteRow != null ? deleteRow : firstOptionRow;
                            bestDeleteRow = deleteRow;
                        }
                    }
                }
            }

            for (int i = 0; i < childCount; i++) {
                View c = vg.getChildAt(i);
                if (c instanceof ViewGroup childVg && c.getVisibility() == View.VISIBLE) {
                    queue.add(childVg);
                }
            }
        }

        if (bestContainer == null || bestSampleRow == null) return null;
        return new MenuTarget(bestContainer, bestSampleRow, bestDeleteRow);
    }

    private static boolean isInsideSheetContainer(View v, View rootGroup, boolean isDialogRoot) {
        for (android.view.ViewParent p = v instanceof ViewGroup ? (ViewGroup) v : v.getParent();
             p instanceof View pv;
             p = pv.getParent()) {
            int id = pv.getId();
            if ((sActionSheetContainerId != 0 && id == sActionSheetContainerId)
                    || (sBottomSheetContainerId != 0 && id == sBottomSheetContainerId)
                    || (sDesignBottomSheetId != 0 && id == sDesignBottomSheetId)) {
                return true;
            }
            String cn = pv.getClass().getName();
            if (cn.contains("BottomSheet") || cn.contains("ActionSheet")) {
                return true;
            }
            if (pv == rootGroup) break;
        }
        if (isDialogRoot && rootGroup != null) {
            Activity act = UIHookManager.getCurrentActivity();
            if (act == null || act.getWindow() == null || act.getWindow().getDecorView() != rootGroup) {
                return true; // separate Dialog / PopupWindow root
            }
        }
        return false;
    }

    private static boolean isRecyclerViewOrListView(View v) {
        if (v == null) return false;
        if (v instanceof android.widget.AbsListView) return true;
        for (Class<?> c = v.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
            String name = c.getName();
            if (name.contains("RecyclerView") || name.contains("ListView")) {
                return true;
            }
        }
        return false;
    }

    private static boolean isInteractive(View v) {
        if (v == null || v.getVisibility() != View.VISIBLE) return false;
        if (v.isClickable() || v.isLongClickable() || v.hasOnClickListeners()) return true;
        if (v instanceof ViewGroup vg) {
            for (int i = 0; i < vg.getChildCount(); i++) {
                if (isInteractive(vg.getChildAt(i))) return true;
            }
        }
        return false;
    }

    private static void insertRowIntoTarget(MenuTarget target, View unsendRow, ViewGroup rootGroup) {
        ViewGroup listGroup = target.rowListGroup;

        // Case 1: The option rows sit directly inside a vertical LinearLayout (not a RecyclerView)
        if (listGroup instanceof LinearLayout ll
                && ll.getOrientation() == LinearLayout.VERTICAL
                && !isRecyclerViewOrListView(listGroup)) {
            if (target.deleteRow != null && target.deleteRow.getParent() == ll) {
                int idx = ll.indexOfChild(target.deleteRow);
                ll.addView(unsendRow, Math.min(idx + 1, ll.getChildCount()));
            } else {
                ll.addView(unsendRow);
            }
            return;
        }

        // Case 2: The option rows sit inside a RecyclerView or ListView.
        // Walk up ancestors inside the sheet to find a vertical LinearLayout (e.g. the sheet
        // container holding the drag handle/header + RecyclerView) and insert unsendRow right
        // ABOVE the RecyclerView (at idx) so it is always visible on screen and never clipped!
        View childInLinear = listGroup;
        View current = listGroup;
        for (int depth = 0; depth < 6 && current != rootGroup && current.getParent() instanceof ViewGroup parent; depth++) {
            if (parent instanceof LinearLayout ll
                    && ll.getOrientation() == LinearLayout.VERTICAL
                    && !isRecyclerViewOrListView(parent)) {
                int idx = ll.indexOfChild(childInLinear);
                ll.addView(unsendRow, Math.max(0, idx));
                return;
            }
            childInLinear = parent;
            current = parent;
        }

        // Case 3: Fallback when listGroup's parent is a FrameLayout / ConstraintLayout / CoordinatorLayout
        // without an enclosing vertical LinearLayout. Never detach listGroup! Instead, add top padding
        // to listGroup so its rows shift down by one row height, and overlay unsendRow at the top.
        if (listGroup.getParent() instanceof ViewGroup parent) {
            Context ctx = listGroup.getContext();
            int rowH = target.sampleRow.getHeight() > 0 ? target.sampleRow.getHeight() : dp(ctx, 52);
            listGroup.setClipToPadding(false);
            listGroup.setPadding(
                    listGroup.getPaddingLeft(),
                    listGroup.getPaddingTop() + rowH,
                    listGroup.getPaddingRight(),
                    listGroup.getPaddingBottom());
            try {
                listGroup.scrollBy(0, -rowH);
            } catch (Throwable ignored) {}

            ViewGroup.MarginLayoutParams lp = new ViewGroup.MarginLayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, rowH);
            lp.topMargin = listGroup.getTop();
            unsendRow.setLayoutParams(lp);
            unsendRow.setElevation(dp(ctx, 4));
            parent.addView(unsendRow);
        }
    }

    /**
     * Builds a row styled identically to Instagram's native bottom-sheet action rows, using
     * destructive red (#FF453A or the Delete row's exact text color).
     */
    private static View buildUnsendMenuRow(Context ctx, View sampleRow, View.OnClickListener onClick) {
        TextView sampleTv = findPrimaryTextView(sampleRow);
        ImageView sampleIcon = findPrimaryImageView(sampleRow);

        int destructiveColor = Color.parseColor("#FF453A");
        if (sampleTv != null) {
            int sampleColor = sampleTv.getCurrentTextColor();
            // If sampleRow is already a red destructive row ("Delete"), match its exact shade
            if (Color.red(sampleColor) > 180 && Color.green(sampleColor) < 110 && Color.blue(sampleColor) < 110) {
                destructiveColor = sampleColor;
            }
        }

        LinearLayout row = new LinearLayout(ctx);
        row.setTag(MENU_ITEM_TAG);
        row.setOrientation(LinearLayout.HORIZONTAL);
        row.setGravity(Gravity.CENTER_VERTICAL);
        row.setClickable(true);
        row.setFocusable(true);

        int minHeight = sampleRow.getHeight() > 0 ? sampleRow.getHeight() : dp(ctx, 52);
        row.setMinimumHeight(minHeight);

        int padL = sampleRow.getPaddingLeft() > 0 ? sampleRow.getPaddingLeft() : dp(ctx, 16);
        int padR = sampleRow.getPaddingRight() > 0 ? sampleRow.getPaddingRight() : dp(ctx, 16);
        int padT = sampleRow.getPaddingTop() > 0 ? sampleRow.getPaddingTop() : dp(ctx, 12);
        int padB = sampleRow.getPaddingBottom() > 0 ? sampleRow.getPaddingBottom() : dp(ctx, 12);
        row.setPadding(padL, padT, padR, padB);

        // Press ripple
        StateListDrawable bg = new StateListDrawable();
        bg.addState(new int[]{android.R.attr.state_pressed}, new ColorDrawable(0x22888888));
        bg.addState(new int[]{}, new ColorDrawable(Color.TRANSPARENT));
        try {
            row.setBackground(new RippleDrawable(ColorStateList.valueOf(0x22888888), null,
                    new ColorDrawable(Color.WHITE)));
        } catch (Throwable t) {
            row.setBackground(bg);
        }

        TextView label = new TextView(ctx);
        String text = I18n.t(ctx, R.string.ig_unsend_all_menu_option);
        if (text == null || text.isEmpty()) text = "Unsend all messages";
        label.setText(text);
        label.setTextColor(destructiveColor);
        if (sampleTv != null) {
            label.setTextSize(TypedValue.COMPLEX_UNIT_PX, sampleTv.getTextSize());
            label.setTypeface(sampleTv.getTypeface(),
                    sampleTv.getTypeface() != null ? sampleTv.getTypeface().getStyle() : Typeface.NORMAL);
            label.setPadding(sampleTv.getPaddingLeft(), sampleTv.getPaddingTop(),
                    sampleTv.getPaddingRight(), sampleTv.getPaddingBottom());
        } else {
            label.setTextSize(TypedValue.COMPLEX_UNIT_SP, 16);
        }

        LinearLayout.LayoutParams tvLp = new LinearLayout.LayoutParams(
                0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f);
        if (sampleTv != null && sampleTv.getLayoutParams() instanceof ViewGroup.MarginLayoutParams mlp) {
            tvLp.leftMargin = mlp.leftMargin;
            tvLp.rightMargin = mlp.rightMargin;
        }
        label.setLayoutParams(tvLp);

        // If sibling rows have an icon, add a matching trash/unsend icon in the same relative position
        ImageView iconView = null;
        boolean iconOnLeft = true;
        if (sampleIcon != null && sampleIcon.getVisibility() == View.VISIBLE) {
            Drawable d = DialogUtils.moduleIcon(R.drawable.ic_delete, destructiveColor);
            if (d != null) {
                iconView = new ImageView(ctx);
                iconView.setImageDrawable(d);
                iconView.setScaleType(ImageView.ScaleType.CENTER_INSIDE);
                int w = sampleIcon.getWidth() > 0 ? sampleIcon.getWidth() : dp(ctx, 24);
                int h = sampleIcon.getHeight() > 0 ? sampleIcon.getHeight() : dp(ctx, 24);
                LinearLayout.LayoutParams iconLp = new LinearLayout.LayoutParams(w, h);
                if (sampleIcon.getLayoutParams() instanceof ViewGroup.MarginLayoutParams imlp) {
                    iconLp.leftMargin = imlp.leftMargin;
                    iconLp.rightMargin = imlp.rightMargin;
                } else {
                    iconLp.rightMargin = dp(ctx, 14);
                }
                iconView.setLayoutParams(iconLp);
                if (sampleTv != null && sampleIcon.getLeft() > sampleTv.getLeft()) {
                    iconOnLeft = false;
                }
            }
        }

        if (iconView != null && iconOnLeft) row.addView(iconView);
        row.addView(label);
        if (iconView != null && !iconOnLeft) row.addView(iconView);

        row.setLayoutParams(new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
        row.setOnClickListener(onClick);
        return row;
    }

    private static void dismissMenu(View root) {
        try {
            Dialog d = sLastShownDialog.get();
            if (d != null && d.isShowing()) {
                d.dismiss();
                return;
            }
        } catch (Throwable ignored) {}

        try {
            Activity act = UIHookManager.getCurrentActivity();
            if (act == null && root != null) act = activityFromContext(root.getContext());
            if (act != null) {
                act.onBackPressed();
            }
        } catch (Throwable ignored) {}
    }

    private static String resolveTargetThreadId(ViewGroup sheetGroup) {
        long now = SystemClock.uptimeMillis();
        if (sSelectedThreadId != null && (now - sLastInboxInteractionMs) < 20_000L) {
            return sSelectedThreadId;
        }
        if (sLastStoreLookupThreadId != null && (now - sLastStoreLookupMs) < 12_000L) {
            return sLastStoreLookupThreadId;
        }
        // Check if the active Dialog or Fragment holds a DirectThreadKey in its arguments/fields
        try {
            Dialog d = sLastShownDialog.get();
            if (d != null) {
                Object dtk = findDirectThreadKey(d, 0, Collections.newSetFromMap(new IdentityHashMap<>()), 5);
                String tid = extractThreadIdFromKey(dtk);
                if (tid != null) {
                    sThreadKeyById.put(tid, dtk);
                    return tid;
                }
            }
        } catch (Throwable ignored) {}
        try {
            Activity act = UIHookManager.getCurrentActivity();
            if (act != null) {
                Method getFm = act.getClass().getMethod("getSupportFragmentManager");
                Object fm = getFm.invoke(act);
                if (fm != null) {
                    Object frags = fm.getClass().getMethod("getFragments").invoke(fm);
                    if (frags instanceof List<?> list) {
                        for (int i = list.size() - 1; i >= 0; i--) {
                            Object frag = list.get(i);
                            if (frag == null) continue;
                            Object dtk = findDirectThreadKey(frag, 0, Collections.newSetFromMap(new IdentityHashMap<>()), 5);
                            String tid = extractThreadIdFromKey(dtk);
                            if (tid != null) {
                                sThreadKeyById.put(tid, dtk);
                                return tid;
                            }
                        }
                    }
                }
            }
        } catch (Throwable ignored) {}
        // Check if the sheet itself has a header TextView matching a known thread title
        if (sheetGroup != null) {
            List<String> texts = new ArrayList<>();
            collectVisibleTexts(sheetGroup, texts, 15);
            for (String t : texts) {
                String id = sThreadIdByNormalizedTitle.get(normalizeTitle(t));
                if (id != null) return id;
            }
        }
        if (sSelectedThreadTitle != null) {
            String id = sThreadIdByNormalizedTitle.get(normalizeTitle(sSelectedThreadTitle));
            if (id != null) return id;
        }
        return sSelectedThreadId != null ? sSelectedThreadId : sLastStoreLookupThreadId;
    }

    private static String resolveTargetThreadTitle(String threadId, ViewGroup sheetGroup) {
        if (threadId != null) {
            String t = sTitleByThreadId.get(threadId);
            if (t != null && !t.isEmpty()) return t;
            t = ThreadNames.get(threadId);
            if (t != null && !t.isEmpty()) return t;
        }
        if (sSelectedThreadTitle != null && !sSelectedThreadTitle.isEmpty()) {
            return sSelectedThreadTitle;
        }
        return null;
    }

    // ── 5. Confirmation & Progress Dialogs + Full Unsend Execution ───────────

    private static void showConfirmationDialog(Context ctx, String threadId, Object threadKey, String chatTitle) {
        if (threadId == null || threadId.isEmpty()) {
            String err = I18n.t(ctx, R.string.ig_unsend_all_error_no_thread);
            if (err.isEmpty()) err = "Could not identify this chat. Try opening it once first.";
            Toast.makeText(ctx, err, Toast.LENGTH_SHORT).show();
            return;
        }

        try {
            LinearLayout card = new LinearLayout(ctx);
            card.setOrientation(LinearLayout.VERTICAL);
            int pad = dp(ctx, 22);
            card.setPadding(pad, pad, pad, dp(ctx, 18));
            GradientDrawable bg = new GradientDrawable();
            bg.setColor(Color.parseColor("#1C1C1E"));
            bg.setCornerRadius(dp(ctx, 20));
            bg.setStroke(Math.max(1, dp(ctx, 1)), Color.parseColor("#2EFFFFFF"));
            card.setBackground(bg);

            TextView titleView = new TextView(ctx);
            String titleStr = I18n.t(ctx, R.string.ig_unsend_all_confirm_title);
            if (titleStr.isEmpty()) titleStr = "Unsend All Messages?";
            titleView.setText(titleStr);
            titleView.setTextColor(Color.WHITE);
            titleView.setTextSize(TypedValue.COMPLEX_UNIT_SP, 18);
            titleView.setTypeface(null, Typeface.BOLD);
            card.addView(titleView);

            TextView msgView = new TextView(ctx);
            String msgStr;
            if (chatTitle != null && !chatTitle.trim().isEmpty()) {
                msgStr = I18n.t(ctx, R.string.ig_unsend_all_confirm_message_named, chatTitle.trim());
                if (msgStr.isEmpty()) {
                    msgStr = "Are you sure you want to unsend all of your sent messages in \""
                            + chatTitle.trim() + "\"? This action cannot be undone.";
                }
            } else {
                msgStr = I18n.t(ctx, R.string.ig_unsend_all_confirm_message);
                if (msgStr.isEmpty()) {
                    msgStr = "Are you sure you want to unsend all of your sent messages in this chat? This action cannot be undone.";
                }
            }
            msgView.setText(msgStr);
            msgView.setTextColor(Color.parseColor("#EBEBF5"));
            msgView.setTextSize(TypedValue.COMPLEX_UNIT_SP, 14);
            msgView.setPadding(0, dp(ctx, 10), 0, dp(ctx, 20));
            card.addView(msgView);

            LinearLayout btnRow = new LinearLayout(ctx);
            btnRow.setOrientation(LinearLayout.HORIZONTAL);
            btnRow.setGravity(Gravity.END);

            TextView cancelBtn = buildDialogButton(ctx,
                    ctx.getString(android.R.string.cancel),
                    Color.parseColor("#2C2C2E"), Color.WHITE);

            String confirmLabel = I18n.t(ctx, R.string.ig_unsend_all_confirm_action);
            if (confirmLabel.isEmpty()) confirmLabel = "Unsend All";
            TextView confirmBtn = buildDialogButton(ctx,
                    confirmLabel,
                    Color.parseColor("#FF453A"), Color.WHITE);
            LinearLayout.LayoutParams confirmLp = new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
            confirmLp.leftMargin = dp(ctx, 10);
            confirmBtn.setLayoutParams(confirmLp);

            btnRow.addView(cancelBtn);
            btnRow.addView(confirmBtn);
            card.addView(btnRow);

            AlertDialog dialog = new AlertDialog.Builder(ctx)
                    .setView(card)
                    .setCancelable(true)
                    .create();
            if (dialog.getWindow() != null) {
                dialog.getWindow().setBackgroundDrawable(new ColorDrawable(Color.TRANSPARENT));
            }

            cancelBtn.setOnClickListener(v -> dialog.dismiss());
            confirmBtn.setOnClickListener(v -> {
                dialog.dismiss();
                startUnsendAllProcess(ctx, threadId, threadKey);
            });

            dialog.show();
        } catch (Throwable t) {
            ModuleLog.line("(IE|UnsendAll) ❌ showConfirmationDialog: " + t.getMessage());
        }
    }

    private static TextView buildDialogButton(Context ctx, String text, int bgColor, int textColor) {
        TextView btn = new TextView(ctx);
        btn.setText(text);
        btn.setTextColor(textColor);
        btn.setTextSize(TypedValue.COMPLEX_UNIT_SP, 14);
        btn.setTypeface(null, Typeface.BOLD);
        btn.setGravity(Gravity.CENTER);
        btn.setPadding(dp(ctx, 18), dp(ctx, 10), dp(ctx, 18), dp(ctx, 10));
        GradientDrawable bg = new GradientDrawable();
        bg.setColor(bgColor);
        bg.setCornerRadius(dp(ctx, 12));
        btn.setBackground(bg);
        btn.setClickable(true);
        btn.setFocusable(true);
        return btn;
    }

    private static void startUnsendAllProcess(Context ctx, String threadId, Object threadKey) {
        final AtomicBoolean cancelled = new AtomicBoolean(false);

        LinearLayout card = new LinearLayout(ctx);
        card.setOrientation(LinearLayout.VERTICAL);
        int pad = dp(ctx, 22);
        card.setPadding(pad, pad, pad, dp(ctx, 18));
        GradientDrawable bg = new GradientDrawable();
        bg.setColor(Color.parseColor("#1C1C1E"));
        bg.setCornerRadius(dp(ctx, 20));
        bg.setStroke(Math.max(1, dp(ctx, 1)), Color.parseColor("#2EFFFFFF"));
        card.setBackground(bg);

        TextView titleView = new TextView(ctx);
        String titleStr = I18n.t(ctx, R.string.ig_unsend_all_progress_title);
        if (titleStr.isEmpty()) titleStr = "Unsending Messages…";
        titleView.setText(titleStr);
        titleView.setTextColor(Color.WHITE);
        titleView.setTextSize(TypedValue.COMPLEX_UNIT_SP, 18);
        titleView.setTypeface(null, Typeface.BOLD);
        card.addView(titleView);

        final TextView statusView = new TextView(ctx);
        String initStatus = I18n.t(ctx, R.string.ig_unsend_all_scanning, 0);
        if (initStatus.isEmpty()) initStatus = "Scanning chat history… (0 found)";
        statusView.setText(initStatus);
        statusView.setTextColor(Color.parseColor("#EBEBF5"));
        statusView.setTextSize(TypedValue.COMPLEX_UNIT_SP, 14);
        statusView.setPadding(0, dp(ctx, 12), 0, dp(ctx, 12));
        card.addView(statusView);

        final ProgressBar progressBar = new ProgressBar(ctx, null, android.R.attr.progressBarStyleHorizontal);
        progressBar.setIndeterminate(true);
        progressBar.setProgressTintList(ColorStateList.valueOf(Color.parseColor("#5E5CE6")));
        progressBar.setIndeterminateTintList(ColorStateList.valueOf(Color.parseColor("#5E5CE6")));
        LinearLayout.LayoutParams pbLp = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        pbLp.bottomMargin = dp(ctx, 16);
        progressBar.setLayoutParams(pbLp);
        card.addView(progressBar);

        LinearLayout btnRow = new LinearLayout(ctx);
        btnRow.setOrientation(LinearLayout.HORIZONTAL);
        btnRow.setGravity(Gravity.END);
        TextView cancelBtn = buildDialogButton(ctx,
                ctx.getString(android.R.string.cancel),
                Color.parseColor("#2C2C2E"), Color.WHITE);
        btnRow.addView(cancelBtn);
        card.addView(btnRow);

        final AlertDialog progressDialog = new AlertDialog.Builder(ctx)
                .setView(card)
                .setCancelable(false)
                .create();
        if (progressDialog.getWindow() != null) {
            progressDialog.getWindow().setBackgroundDrawable(new ColorDrawable(Color.TRANSPARENT));
        }

        cancelBtn.setOnClickListener(v -> {
            cancelled.set(true);
            cancelBtn.setEnabled(false);
            cancelBtn.setAlpha(0.5f);
        });

        progressDialog.show();

        executor.submit(() -> runUnsendWorker(ctx, threadId, threadKey, cancelled,
                progressDialog, statusView, progressBar));
    }

    private static void runUnsendWorker(Context ctx, String threadId, Object threadKey,
                                        AtomicBoolean cancelled, AlertDialog progressDialog,
                                        TextView statusView, ProgressBar progressBar) {
        int totalUnsent = 0;
        try {
            // Ensure current user ID is resolved if possible
            if (sCurrentUserId == null && sDirectThreadStore != null) {
                extractUserSessionFromObject(sDirectThreadStore);
            }

            LinkedHashSet<String> allMyMessageIds = new LinkedHashSet<>();

            // 1. Collect any locally cached messages in DirectThreadStore for this thread
            if (sCurrentUserId != null) {
                collectLocalCachedMessageIds(threadKey, threadId, sCurrentUserId, allMyMessageIds);
            }

            // 2. Paginate through the entire server thread history
            String cursor = null;
            Set<String> visitedCursors = new HashSet<>();
            int pageCount = 0;
            int maxPages = 250; // up to ~5,000-7,500 messages in a thread

            while (!cancelled.get() && pageCount < maxPages) {
                pageCount++;
                String jsonStr = fetchThreadPageJson(threadId, cursor, cancelled);
                if (jsonStr == null || jsonStr.isEmpty()) break;

                JSONObject root = new JSONObject(jsonStr);
                JSONObject thread = root.optJSONObject("thread");
                if (thread == null) break;

                // Resolve viewer_id from thread payload if sCurrentUserId wasn't known yet
                String viewerId = optIdString(thread, "viewer_id");
                if (sCurrentUserId == null && !viewerId.isEmpty()) {
                    sCurrentUserId = viewerId;
                    collectLocalCachedMessageIds(threadKey, threadId, sCurrentUserId, allMyMessageIds);
                }
                String myUid = sCurrentUserId != null ? sCurrentUserId : viewerId;

                JSONArray items = thread.optJSONArray("items");
                if (items != null && myUid != null && !myUid.isEmpty()) {
                    for (int i = 0; i < items.length(); i++) {
                        JSONObject item = items.optJSONObject(i);
                        if (item == null) continue;
                        String itemType = item.optString("item_type", "");
                        if ("action_log".equals(itemType) || "video_call_event".equals(itemType)) {
                            continue;
                        }
                        String senderId = optIdString(item, "user_id");
                        String itemId = optIdString(item, "item_id");
                        if (!itemId.isEmpty() && myUid.equals(senderId)) {
                            allMyMessageIds.add(itemId);
                        }
                    }
                }

                final int foundSoFar = allMyMessageIds.size();
                mainHandler.post(() -> {
                    String s = I18n.t(ctx, R.string.ig_unsend_all_scanning, foundSoFar);
                    if (s.isEmpty()) s = "Scanning chat history… (" + foundSoFar + " found)";
                    statusView.setText(s);
                });

                boolean hasOlder = thread.optBoolean("has_older", false);
                String nextCursor = thread.optString("oldest_cursor", "");
                if (nextCursor.isEmpty() || "null".equals(nextCursor)) {
                    nextCursor = thread.optString("prev_cursor", "");
                }
                if (!hasOlder || nextCursor.isEmpty() || "null".equals(nextCursor)
                        || !visitedCursors.add(nextCursor)) {
                    break;
                }
                cursor = nextCursor;
                sleepInterruptibly(220, cancelled);
            }

            if (cancelled.get()) {
                finishOnUi(ctx, progressDialog, R.string.ig_unsend_all_cancelled, totalUnsent);
                return;
            }

            if (allMyMessageIds.isEmpty()) {
                mainHandler.post(() -> {
                    try { progressDialog.dismiss(); } catch (Throwable ignored) {}
                    String msg = I18n.t(ctx, R.string.ig_unsend_all_none_found);
                    if (msg.isEmpty()) msg = "No sent messages found to unsend";
                    Toast.makeText(ctx, msg, Toast.LENGTH_SHORT).show();
                });
                return;
            }

            // 3. Unsend all discovered messages one by one with progress updates
            final int totalToUnsend = allMyMessageIds.size();
            mainHandler.post(() -> {
                progressBar.setIndeterminate(false);
                progressBar.setMax(totalToUnsend);
                progressBar.setProgress(0);
            });

            int index = 0;
            for (String itemId : allMyMessageIds) {
                if (cancelled.get()) break;
                index++;
                final int curIdx = index;
                mainHandler.post(() -> {
                    progressBar.setProgress(curIdx);
                    String s = I18n.t(ctx, R.string.ig_unsend_all_progress_count, curIdx, totalToUnsend);
                    if (s.isEmpty()) s = "Unsending messages… (" + curIdx + " / " + totalToUnsend + ")";
                    statusView.setText(s);
                });

                boolean ok = deleteThreadItemOnServer(threadId, itemId, cancelled);
                if (ok) {
                    totalUnsent++;
                    KeepUnsentMessagesHook.allowAndPurgeSelfUnsent(itemId);
                    removeMessageFromLocalStore(threadKey, threadId, itemId);
                }

                sleepInterruptibly(200, cancelled);
            }

            if (cancelled.get()) {
                finishOnUi(ctx, progressDialog, R.string.ig_unsend_all_cancelled, totalUnsent);
            } else {
                finishOnUi(ctx, progressDialog, R.string.ig_unsend_all_completed, totalUnsent);
            }
        } catch (Throwable t) {
            ModuleLog.line("(IE|UnsendAll) ❌ worker error: " + t);
            final int count = totalUnsent;
            mainHandler.post(() -> {
                try { progressDialog.dismiss(); } catch (Throwable ignored) {}
                String msg = I18n.t(ctx, R.string.ig_unsend_all_completed, count);
                if (msg.isEmpty()) msg = "Unsent " + count + " messages";
                Toast.makeText(ctx, msg, Toast.LENGTH_SHORT).show();
            });
        }
    }

    private static void finishOnUi(Context ctx, AlertDialog dialog, int resId, int count) {
        mainHandler.post(() -> {
            try { dialog.dismiss(); } catch (Throwable ignored) {}
            String msg = I18n.t(ctx, resId, count);
            if (msg.isEmpty()) {
                msg = (resId == R.string.ig_unsend_all_cancelled)
                        ? "Cancelled (" + count + " messages unsent)"
                        : "Unsent " + count + " messages";
            }
            Toast.makeText(ctx, msg, Toast.LENGTH_SHORT).show();
        });
    }

    // ── 6. Instagram Direct REST API Calls (GET Thread & POST Delete Item) ───

    private static String fetchThreadPageJson(String threadId, String cursor, AtomicBoolean cancelled) {
        for (int attempt = 0; attempt < 3 && !cancelled.get(); attempt++) {
            HttpURLConnection conn = null;
            try {
                StringBuilder urlSb = new StringBuilder("https://i.instagram.com/api/v1/direct_v2/threads/")
                        .append(threadId)
                        .append("/?visual_message_return_type=unseen&direction=older");
                if (cursor != null && !cursor.isEmpty()) {
                    urlSb.append("&cursor=").append(URLEncoder.encode(cursor, "UTF-8"));
                }

                conn = (HttpURLConnection) new URL(urlSb.toString()).openConnection();
                conn.setRequestMethod("GET");
                conn.setConnectTimeout(12_000);
                conn.setReadTimeout(12_000);
                applyInstagramHeaders(conn);

                int code = conn.getResponseCode();
                if (code == 200) {
                    return readStream(conn);
                } else if (code == 429 || code >= 500) {
                    ModuleLog.line("(IE|UnsendAll) ⚠️ GET thread HTTP " + code + ", backing off");
                    sleepInterruptibly(2500L * (attempt + 1), cancelled);
                } else {
                    ModuleLog.line("(IE|UnsendAll) ❌ GET thread HTTP " + code);
                    return null;
                }
            } catch (Throwable t) {
                ModuleLog.line("(IE|UnsendAll) ⚠️ GET thread exception: " + t.getMessage());
                sleepInterruptibly(1500L, cancelled);
            } finally {
                if (conn != null) conn.disconnect();
            }
        }
        return null;
    }

    private static boolean deleteThreadItemOnServer(String threadId, String itemId, AtomicBoolean cancelled) {
        for (int attempt = 0; attempt < 3 && !cancelled.get(); attempt++) {
            HttpURLConnection conn = null;
            try {
                String urlStr = "https://i.instagram.com/api/v1/direct_v2/threads/"
                        + threadId + "/items/" + itemId + "/delete/";
                conn = (HttpURLConnection) new URL(urlStr).openConnection();
                conn.setRequestMethod("POST");
                conn.setDoOutput(true);
                conn.setConnectTimeout(12_000);
                conn.setReadTimeout(12_000);
                applyInstagramHeaders(conn);
                conn.setRequestProperty("Content-Type", "application/x-www-form-urlencoded; charset=UTF-8");

                String uuid = sCapturedHeaders.get("X-IG-Device-ID");
                if (uuid == null || uuid.isEmpty()) uuid = UUID.randomUUID().toString();
                byte[] body = ("_uuid=" + URLEncoder.encode(uuid, "UTF-8") + "&_csrftoken=missing")
                        .getBytes(StandardCharsets.UTF_8);
                conn.setFixedLengthStreamingMode(body.length);
                try (OutputStream os = conn.getOutputStream()) {
                    os.write(body);
                }

                int code = conn.getResponseCode();
                if (code >= 200 && code < 300) {
                    return true;
                } else if (code == 429 || code >= 500) {
                    ModuleLog.line("(IE|UnsendAll) ⚠️ DELETE item HTTP " + code + ", backing off");
                    sleepInterruptibly(2500L * (attempt + 1), cancelled);
                } else {
                    ModuleLog.line("(IE|UnsendAll) ⚠️ DELETE item HTTP " + code + " for item=" + itemId);
                    return false;
                }
            } catch (Throwable t) {
                ModuleLog.line("(IE|UnsendAll) ⚠️ DELETE exception: " + t.getMessage());
                sleepInterruptibly(1500L, cancelled);
            } finally {
                if (conn != null) conn.disconnect();
            }
        }
        return false;
    }

    private static void applyInstagramHeaders(HttpURLConnection conn) {
        for (Map.Entry<String, String> e : sCapturedHeaders.entrySet()) {
            conn.setRequestProperty(e.getKey(), e.getValue());
        }
        conn.setRequestProperty("Accept-Encoding", "gzip");
        if (!sCapturedHeaders.containsKey("X-IG-App-ID")) {
            conn.setRequestProperty("X-IG-App-ID", "567067343352427");
        }
    }

    private static String readStream(HttpURLConnection conn) throws Exception {
        InputStream in = conn.getInputStream();
        String encoding = conn.getContentEncoding();
        if (encoding != null && encoding.toLowerCase(Locale.US).contains("gzip")) {
            in = new GZIPInputStream(in);
        }
        try (InputStream stream = in; ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
            byte[] buf = new byte[8192];
            int n;
            while ((n = stream.read(buf)) != -1) {
                bos.write(buf, 0, n);
            }
            return bos.toString("UTF-8");
        }
    }

    private static String optIdString(JSONObject obj, String key) {
        if (obj == null || !obj.has(key) || obj.isNull(key)) return "";
        Object val = obj.opt(key);
        return val != null ? String.valueOf(val).trim() : "";
    }

    private static void sleepInterruptibly(long ms, AtomicBoolean cancelled) {
        long end = SystemClock.uptimeMillis() + ms;
        while (!cancelled.get() && SystemClock.uptimeMillis() < end) {
            try {
                Thread.sleep(Math.min(100L, end - SystemClock.uptimeMillis()));
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return;
            }
        }
    }

    // ── 7. Local DirectThreadStore Inspection & Cleanup ──────────────────────

    private static void collectLocalCachedMessageIds(Object threadKey, String threadId,
                                                     String myUserId, Set<String> outIds) {
        try {
            Object store = sDirectThreadStore;
            Object dtk = threadKey != null ? threadKey : sThreadKeyById.get(threadId);
            if (store == null || dtk == null || myUserId == null) return;

            for (Method lookup : sThreadLookupMethods) {
                try {
                    Object entry = lookup.invoke(store, dtk);
                    if (entry == null) continue;
                    for (Class<?> c = entry.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
                        for (Field f : c.getDeclaredFields()) {
                            if (Modifier.isStatic(f.getModifiers()) || !List.class.isAssignableFrom(f.getType())) {
                                continue;
                            }
                            f.setAccessible(true);
                            Object listObj = f.get(entry);
                            if (!(listObj instanceof List<?> msgList) || msgList.isEmpty()) continue;
                            for (Object msg : new ArrayList<>(msgList)) {
                                extractMyItemIdFromMessageModel(msg, myUserId, threadId, outIds);
                            }
                        }
                    }
                } catch (Throwable ignored) {}
            }
        } catch (Throwable ignored) {}
    }

    private static void extractMyItemIdFromMessageModel(Object msg, String myUserId,
                                                        String threadId, Set<String> outIds) {
        if (msg == null) return;
        boolean sentByMe = false;
        List<String> candidateItemIds = new ArrayList<>();

        for (Class<?> c = msg.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
            for (Field f : c.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers()) || f.getType() != String.class) continue;
                try {
                    f.setAccessible(true);
                    String val = (String) f.get(msg);
                    if (val == null) continue;
                    if (val.equals(myUserId)) {
                        sentByMe = true;
                    } else if (val.length() >= 18 && val.length() <= 40
                            && !val.equals(threadId) && val.chars().allMatch(Character::isDigit)) {
                        candidateItemIds.add(val);
                    }
                } catch (Throwable ignored) {}
            }
        }

        if (sentByMe && !candidateItemIds.isEmpty()) {
            outIds.add(candidateItemIds.get(0));
        }
    }

    private static void removeMessageFromLocalStore(Object threadKey, String threadId, String itemId) {
        final Object store = sDirectThreadStore;
        final Object dtk = threadKey != null ? threadKey : sThreadKeyById.get(threadId);
        if (store == null || dtk == null || itemId == null) return;

        mainHandler.post(() -> {
            try {
                if (sRemoveMethod3 != null) {
                    sRemoveMethod3.invoke(store, dtk, itemId, "unsend");
                } else if (sRemoveMethod4 != null) {
                    sRemoveMethod4.invoke(store, dtk, itemId, "unsend", true);
                }
            } catch (Throwable ignored) {}
        });
    }

    // ── 8. Reflection & View Tree Helpers ────────────────────────────────────

    private static Object findDirectThreadKey(Object obj, int depth, Set<Object> seen, int maxDepth) {
        if (obj == null || depth > maxDepth || !seen.add(obj)) return null;
        String cn = obj.getClass().getName();
        if (cn.equals(DTK_CLASS) || cn.contains("DirectThreadKey")) return obj;
        if (obj instanceof android.os.Bundle bundle) {
            try {
                for (String k : bundle.keySet()) {
                    Object hit = findDirectThreadKey(bundle.get(k), depth + 1, seen, maxDepth);
                    if (hit != null) return hit;
                }
            } catch (Throwable ignored) {}
            return null;
        }
        if (obj instanceof View v) {
            Object tag = v.getTag();
            if (tag != null) {
                Object hit = findDirectThreadKey(tag, depth + 1, seen, maxDepth);
                if (hit != null) return hit;
            }
        }
        boolean descend = cn.startsWith("X.") || cn.startsWith("com.instagram.")
                || cn.startsWith("androidx.fragment.")
                || obj instanceof View || obj instanceof Dialog;
        if (!descend) return null;

        for (Class<?> c = obj.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
            String cname = c.getName();
            if (cname.startsWith("java.")) break;
            for (Field f : c.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers()) || f.getType().isPrimitive()) continue;
                try {
                    f.setAccessible(true);
                    Object v = f.get(obj);
                    Object hit = findDirectThreadKey(v, depth + 1, seen, maxDepth);
                    if (hit != null) return hit;
                } catch (Throwable ignored) {}
            }
        }
        return null;
    }

    private static String findKnownThreadIdInGraph(Object obj, int depth, Set<Object> seen, int maxDepth) {
        if (obj == null || depth > maxDepth || !seen.add(obj)) return null;
        if (obj instanceof String s) {
            if (sThreadKeyById.containsKey(s)) return s;
            return null;
        }
        if (obj instanceof android.os.Bundle bundle) {
            try {
                for (String k : bundle.keySet()) {
                    String hit = findKnownThreadIdInGraph(bundle.get(k), depth + 1, seen, maxDepth);
                    if (hit != null) return hit;
                }
            } catch (Throwable ignored) {}
            return null;
        }
        String cn = obj.getClass().getName();
        boolean descend = cn.startsWith("X.") || cn.startsWith("com.instagram.")
                || cn.startsWith("androidx.fragment.")
                || obj instanceof View || obj instanceof Dialog;
        if (!descend) return null;

        for (Class<?> c = obj.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
            String cname = c.getName();
            if (cname.startsWith("java.")) break;
            for (Field f : c.getDeclaredFields()) {
                if (Modifier.isStatic(f.getModifiers()) || f.getType().isPrimitive()) continue;
                try {
                    f.setAccessible(true);
                    Object v = f.get(obj);
                    if (v instanceof String s && sThreadKeyById.containsKey(s)) {
                        return s;
                    } else if (v != null && !(v instanceof String)) {
                        String hit = findKnownThreadIdInGraph(v, depth + 1, seen, maxDepth);
                        if (hit != null) return hit;
                    }
                } catch (Throwable ignored) {}
            }
        }
        return null;
    }

    private static String extractThreadIdFromKey(Object dtk) {
        if (dtk == null) return null;
        try {
            for (Class<?> c = dtk.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
                for (Field f : c.getDeclaredFields()) {
                    if (Modifier.isStatic(f.getModifiers()) || f.getType() != String.class) continue;
                    f.setAccessible(true);
                    Object v = f.get(dtk);
                    if (v instanceof String s && !s.isEmpty()) return s;
                }
            }
        } catch (Throwable ignored) {}
        return null;
    }

    private static TextView findPrimaryTextView(View v) {
        if (v == null || v.getVisibility() != View.VISIBLE) return null;
        if (v instanceof TextView tv) {
            CharSequence cs = tv.getText();
            if (cs != null && !cs.toString().trim().isEmpty()) return tv;
            return null;
        }
        if (v instanceof ViewGroup vg) {
            for (int i = 0; i < vg.getChildCount(); i++) {
                TextView found = findPrimaryTextView(vg.getChildAt(i));
                if (found != null) {
                    return found;
                }
            }
        }
        return null;
    }

    private static ImageView findPrimaryImageView(View v) {
        if (v == null || v.getVisibility() != View.VISIBLE) return null;
        if (v instanceof ImageView iv) return iv;
        if (v instanceof ViewGroup vg) {
            for (int i = 0; i < vg.getChildCount(); i++) {
                ImageView found = findPrimaryImageView(vg.getChildAt(i));
                if (found != null) return found;
            }
        }
        return null;
    }

    private static void collectVisibleTexts(View v, List<String> out, int limit) {
        if (v == null || v.getVisibility() != View.VISIBLE || out.size() >= limit) return;
        if (v instanceof TextView tv) {
            CharSequence cs = tv.getText();
            if (cs != null) {
                String s = cs.toString().trim();
                if (s.length() >= 2 && s.length() <= 60 && !out.contains(s)) {
                    out.add(s);
                }
            }
        }
        CharSequence cd = v.getContentDescription();
        if (cd != null) {
            String s = cd.toString().trim();
            if (s.length() >= 2 && s.length() <= 60 && !out.contains(s)) {
                out.add(s);
            }
        }
        if (v instanceof ViewGroup vg) {
            for (int i = 0; i < vg.getChildCount() && out.size() < limit; i++) {
                collectVisibleTexts(vg.getChildAt(i), out, limit);
            }
        }
    }

    @SuppressLint("DiscouragedApi")
    private static void ensureResourceIds(Context ctx) {
        if (ctx == null || sInboxRecyclerId != 0) return;
        try {
            Resources r = ctx.getResources();
            String pkg = ctx.getPackageName();
            sInboxRecyclerId        = r.getIdentifier("inbox_refreshable_thread_list_recyclerview", "id", pkg);
            sInboxActionBarId       = r.getIdentifier("direct_inbox_action_bar", "id", pkg);
            sThreadHeaderId         = r.getIdentifier("direct_thread_header", "id", pkg);
            sActionSheetContainerId = r.getIdentifier("action_sheet_container", "id", pkg);
            sBottomSheetContainerId = r.getIdentifier("bottom_sheet_container", "id", pkg);
            sDesignBottomSheetId    = r.getIdentifier("design_bottom_sheet", "id", pkg);
        } catch (Throwable ignored) {}
    }

    private static Activity activityFromContext(Context ctx) {
        while (ctx instanceof ContextWrapper cw) {
            if (ctx instanceof Activity a) return a;
            ctx = cw.getBaseContext();
        }
        return null;
    }

    private static int dp(Context ctx, int value) {
        return Math.round(value * ctx.getResources().getDisplayMetrics().density);
    }
}
