// no_python: Android owns widget objects, native layout, drawing and input callbacks.
package io.kotlean

import android.app.Activity
import android.text.Editable
import android.text.TextWatcher
import android.view.Gravity
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.ViewTreeObserver
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import java.math.BigInteger
import kotlin.math.roundToInt
import kotlin.math.roundToLong

internal class AndroidRenderer(private val activity: Activity, private val send: (Event) -> Unit) {
    val content = FrameLayout(activity).apply { fitsSystemWindows = true }
    private class Node(val id: BigInteger, val view: View) {
        val nativeClickable = view.isClickable
        var revision: BigInteger = BigInteger.ZERO
        var width: Dimension = Dimension.Wrap
        var height: Dimension = Dimension.Wrap
        var padding: BigInteger = BigInteger.ZERO
        var textSize: BigInteger = BigInteger.valueOf(16)
        var weight: BigInteger = BigInteger.ZERO
        var listeners = ListenerMask(false, false, false, false, false)
        var lastSize: Triple<Int, Int, Int>? = null
    }
    private val nodes = mutableMapOf<BigInteger, Node>()
    private var applying = false

    fun apply(patches: List<Patch>, revision: BigInteger) {
        val focused = content.findFocus()
        applying = true
        try {
            var movesPrepared = false
            for (patch in patches) when (patch) {
                is Patch.Create -> create(patch.id, patch.kind)
                is Patch.SetProperty -> property(node(patch.id), patch.value)
                is Patch.Insert -> {
                    if (!movesPrepared) {
                        for (move in patches.filterIsInstance<Patch.Insert>()) {
                            val moving = node(move.child).view
                            if (moving.parent !== node(move.parent).view) detach(moving)
                        }
                        movesPrepared = true
                    }
                    val parent = node(patch.parent).view as? ViewGroup ?: error("Non-container parent")
                    val child = node(patch.child)
                    val index = patch.index.intValueExact()
                    if (parent.indexOfChild(child.view) != index) {
                        detach(child.view)
                        parent.addView(child.view, index, layout(child, parent))
                    }
                }
                is Patch.Remove -> {
                    val removed = nodes.remove(patch.id) ?: error("Missing removed node")
                    detach(removed.view)
                }
                is Patch.Root -> {
                    val root = patch.id?.let(::node)
                    if (root == null || content.childCount != 1 || content.getChildAt(0) !== root.view) {
                        content.removeAllViews()
                        if (root != null) {
                            detach(root.view)
                            content.addView(root.view, layout(root, content))
                        }
                    }
                }
            }
            for (record in nodes.values) record.revision = revision
            if (focused != null && focused.isAttachedToWindow && !focused.hasFocus()) {
                focused.requestFocus()
            }
        } finally { applying = false }
    }

    private fun node(id: BigInteger): Node = nodes[id] ?: error("Unknown view node: $id")
    private fun detach(view: View) { (view.parent as? ViewGroup)?.removeView(view) }
    private fun emit(record: Node, input: Input) { if (!applying) send(Event.Node(record.revision, record.id, input)) }

    private fun create(id: BigInteger, kind: NodeKind) {
        check(!nodes.containsKey(id)) { "Duplicate view node: $id" }
        val view = when (kind) {
            NodeKind.COLUMN -> LinearLayout(activity).apply { orientation = LinearLayout.VERTICAL }
            NodeKind.ROW -> LinearLayout(activity).apply { orientation = LinearLayout.HORIZONTAL }
            NodeKind.TEXT -> TextView(activity)
            NodeKind.BUTTON -> Button(activity).apply { isAllCaps = false }
            NodeKind.INPUT -> EditText(activity)
            NodeKind.SCROLL -> ScrollView(activity)
            NodeKind.CANVAS -> DrawingView(activity)
        }
        val record = Node(id, view)
        nodes[id] = record
        if (view is EditText) view.addTextChangedListener(object : TextWatcher {
            override fun beforeTextChanged(value: CharSequence?, start: Int, count: Int, after: Int) = Unit
            override fun onTextChanged(value: CharSequence?, start: Int, before: Int, count: Int) = Unit
            override fun afterTextChanged(value: Editable?) {
                emit(record, Input.Text(value?.toString().orEmpty()))
            }
        })
        view.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ -> resize(record) }
        val defaults = listOf(
            Property.Text(""), Property.Hint(""), Property.Foreground(0xffffffffL), Property.Background(0),
            Property.Width(Dimension.Wrap), Property.Height(Dimension.Wrap), Property.Padding(BigInteger.ZERO),
            Property.Weight(BigInteger.ZERO), Property.TextSize(BigInteger.valueOf(16)), Property.Enabled(true),
            Property.Description(""), Property.Align(Alignment.START), Property.Drawing(emptyList()),
            Property.Listeners(ListenerMask(false, false, false, false, false)),
        )
        for (value in defaults) property(record, value)
    }

    private fun dimension(value: Dimension): Int = when (value) {
        Dimension.Wrap -> ViewGroup.LayoutParams.WRAP_CONTENT
        Dimension.Fill -> ViewGroup.LayoutParams.MATCH_PARENT
        is Dimension.Dp -> (value.value.intValueExact() * activity.resources.displayMetrics.density).roundToInt()
    }

    private fun layout(record: Node, parent: ViewGroup?): ViewGroup.LayoutParams = when (parent) {
        is LinearLayout -> LinearLayout.LayoutParams(dimension(record.width), dimension(record.height), record.weight.toFloat())
        is FrameLayout -> FrameLayout.LayoutParams(dimension(record.width), dimension(record.height))
        else -> ViewGroup.LayoutParams(dimension(record.width), dimension(record.height))
    }

    private fun updateLayout(record: Node) {
        record.view.layoutParams = layout(record, record.view.parent as? ViewGroup)
    }

    private fun applyPadding(record: Node) {
        val pixels = (record.padding.intValueExact() *
            record.view.resources.displayMetrics.density).roundToInt()
        record.view.setPadding(pixels, pixels, pixels, pixels)
    }

    private fun applyTextSize(record: Node) {
        (record.view as? TextView)?.textSize = record.textSize.intValueExact().toFloat()
    }

    private fun property(record: Node, value: Property) {
        val view = record.view
        when (value) {
            is Property.Text -> (view as? TextView)?.text = value.value
            is Property.Hint -> (view as? TextView)?.hint = value.value
            is Property.Foreground -> (view as? TextView)?.setTextColor(value.value.toInt())
            is Property.Background -> view.setBackgroundColor(value.value.toInt())
            is Property.Width -> { record.width = value.value; updateLayout(record) }
            is Property.Height -> { record.height = value.value; updateLayout(record) }
            is Property.Padding -> {
                record.padding = value.value
                applyPadding(record)
            }
            is Property.Weight -> { record.weight = value.value; updateLayout(record) }
            is Property.TextSize -> { record.textSize = value.value; applyTextSize(record) }
            is Property.Enabled -> view.isEnabled = value.value
            is Property.Description -> view.contentDescription = value.value
            is Property.Align -> {
                val gravity = when (value.value) {
                    Alignment.START -> Gravity.START or Gravity.TOP
                    Alignment.CENTER -> Gravity.CENTER
                    Alignment.FINISH -> Gravity.END or Gravity.BOTTOM
                }
                (view as? TextView)?.gravity = gravity
                (view as? LinearLayout)?.gravity = gravity
            }
            is Property.Drawing -> (view as? DrawingView)?.operations = value.value
            is Property.Listeners -> listeners(record, value.value)
        }
    }

    private fun listeners(record: Node, mask: ListenerMask) {
        val view = record.view
        record.listeners = mask
        val consumesInput = !mask.click && view !is EditText && view !is ScrollView
        view.setOnClickListener(if (mask.click) View.OnClickListener { emit(record, Input.Click) } else null)
        view.isClickable = mask.click || record.nativeClickable
        view.setOnTouchListener(if (mask.touch) View.OnTouchListener { _, event ->
            val phase = when (event.actionMasked) {
                MotionEvent.ACTION_DOWN, MotionEvent.ACTION_POINTER_DOWN -> TouchPhase.DOWN
                MotionEvent.ACTION_MOVE -> TouchPhase.MOVE
                MotionEvent.ACTION_UP, MotionEvent.ACTION_POINTER_UP -> TouchPhase.UP
                MotionEvent.ACTION_CANCEL -> TouchPhase.CANCEL
                else -> null
            }
            if (phase != null) {
                val contacts = (0 until event.pointerCount).map { index ->
                    Contact(BigInteger.valueOf(event.getPointerId(index).toLong()), Point(
                        BigInteger.valueOf((event.getX(index).toDouble() * 1000).roundToLong()),
                        BigInteger.valueOf((event.getY(index).toDouble() * 1000).roundToLong()),
                    ))
                }
                emit(record, Input.Touch(TouchFrame(phase, BigInteger.valueOf(event.actionIndex.toLong()),
                    BigInteger.valueOf(event.eventTime), contacts)))
            }
            consumesInput
        } else null)
        view.setOnKeyListener(if (mask.key) View.OnKeyListener { _, code, event ->
            emit(record, Input.Key(BigInteger.valueOf(code.toLong()), event.action == android.view.KeyEvent.ACTION_DOWN))
            consumesInput && code != KeyEvent.KEYCODE_TAB
        } else null)
        if (mask.key) view.isFocusableInTouchMode = true
        if (mask.resize) { record.lastSize = null; view.post { resize(record) } }
    }

    private fun resize(record: Node) {
        if (applying) return
        val density = (record.view.resources.displayMetrics.density * 1000).roundToInt()
        val size = Triple(record.view.width, record.view.height, density)
        if (record.listeners.resize && record.lastSize != size) {
            record.lastSize = size
            emit(record, Input.Resize(BigInteger.valueOf(size.first.toLong()),
                BigInteger.valueOf(size.second.toLong()), BigInteger.valueOf(size.third.toLong())))
        }
    }

    fun refreshConfiguration() {
        for (record in nodes.values) {
            updateLayout(record)
            applyPadding(record)
            applyTextSize(record)
        }
        content.viewTreeObserver.addOnGlobalLayoutListener(object : ViewTreeObserver.OnGlobalLayoutListener {
            override fun onGlobalLayout() {
                content.viewTreeObserver.removeOnGlobalLayoutListener(this)
                for (record in nodes.values.toList()) resize(record)
            }
        })
        content.requestLayout()
    }
}
