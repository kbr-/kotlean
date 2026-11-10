// no_python: Android requires an Activity entry point.
package io.kotlean.snacknet

import android.app.Activity
import android.os.Bundle
import io.kotlean.Kotlean

class MainActivity : Activity() {
    override fun onCreate(state: Bundle?) {
        super.onCreate(state)
        Kotlean.run(this, "snacknet", state)
    }
}
