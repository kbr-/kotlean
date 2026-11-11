// no_kotlin: Android requires an Activity entry point.
package io.kotlean.counter

import android.app.Activity
import android.os.Bundle
import io.kotlean.Kotlean

class MainActivity : Activity() {
    override fun onCreate(state: Bundle?) {
        super.onCreate(state)
        Kotlean.run(this, "counter", state)
    }
}
