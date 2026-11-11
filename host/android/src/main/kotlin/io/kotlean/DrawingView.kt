// no_kotlin: Android Canvas is the physical interpreter for the fixed drawing protocol.
package io.kotlean

import android.content.Context
import android.graphics.Canvas
import android.graphics.Paint
import android.graphics.Path
import android.graphics.Typeface
import android.view.View
import java.math.BigInteger

internal class DrawingView(context: Context) : View(context) {
    var operations: List<Draw> = emptyList()
        set(value) {
            val clear = value.indexOfLast { it is Draw.Clear }
            field = if (clear > 0) value.subList(clear, value.size) else value
            invalidate()
        }
    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private fun BigInteger.pixels(): Float = toFloat() / 1000f

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        for (operation in operations) {
            paint.style = Paint.Style.FILL
            when (operation) {
                is Draw.Clear -> canvas.drawColor(operation.color.toInt())
                is Draw.Rect -> {
                    paint.color = operation.color.toInt()
                    val x = operation.origin.x.pixels()
                    val y = operation.origin.y.pixels()
                    canvas.drawRoundRect(x, y, x + operation.width.pixels(), y + operation.height.pixels(),
                        operation.radius.pixels(), operation.radius.pixels(), paint)
                }
                is Draw.Circle -> {
                    paint.color = operation.color.toInt()
                    canvas.drawCircle(operation.center.x.pixels(), operation.center.y.pixels(), operation.radius.pixels(), paint)
                }
                is Draw.Line -> {
                    paint.color = operation.color.toInt()
                    paint.style = Paint.Style.STROKE
                    paint.strokeWidth = operation.width.pixels()
                    canvas.drawLine(operation.start.x.pixels(), operation.start.y.pixels(),
                        operation.finish.x.pixels(), operation.finish.y.pixels(), paint)
                }
                is Draw.Polygon -> {
                    paint.color = operation.color.toInt()
                    val path = Path()
                    operation.points.firstOrNull()?.let { first ->
                        path.moveTo(first.x.pixels(), first.y.pixels())
                        for (point in operation.points.drop(1)) path.lineTo(point.x.pixels(), point.y.pixels())
                        path.close()
                    }
                    canvas.drawPath(path, paint)
                }
                is Draw.Text -> {
                    paint.color = operation.color.toInt()
                    paint.textSize = operation.size.pixels()
                    paint.textAlign = when (operation.alignment) {
                        Alignment.START -> Paint.Align.LEFT
                        Alignment.CENTER -> Paint.Align.CENTER
                        Alignment.FINISH -> Paint.Align.RIGHT
                    }
                    paint.typeface = typeface(operation.weight)
                    canvas.drawText(operation.value, operation.origin.x.pixels(), operation.origin.y.pixels(), paint)
                    paint.textAlign = Paint.Align.LEFT
                    paint.typeface = null
                }
            }
        }
    }

    // Android accepts weights 1 to 1000; a weight outside them draws at the nearest one.
    private val typefaces = HashMap<Int, Typeface>()
    private fun typeface(weight: BigInteger): Typeface {
        val clamped = weight.min(BigInteger.valueOf(1000)).max(BigInteger.ONE).toInt()
        return typefaces.getOrPut(clamped) { Typeface.create(Typeface.DEFAULT, clamped, false) }
    }
}
