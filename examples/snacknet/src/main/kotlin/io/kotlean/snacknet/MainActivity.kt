// no_kotlin: Android requires an Activity entry point.
package io.kotlean.snacknet

import android.app.Activity
import android.os.Build
import android.os.Bundle
import android.view.WindowManager
import io.kotlean.Kotlean

class MainActivity : Activity() {
    override fun onCreate(state: Bundle?) {
        super.onCreate(state)
        if (BuildConfig.DEVICE_TEST) {
            window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
            if (Build.VERSION.SDK_INT >= 27) {
                setShowWhenLocked(true)
                setTurnScreenOn(true)
            }
        }
        Kotlean.run(this, "snacknet", state)
    }
}
