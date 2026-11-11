// no_kotlin: Android and JVM callers require fixed protocol value representations.
package io.kotlean

import java.math.BigInteger

internal class Bytes(value: ByteArray) {
    private val storage = value.copyOf()
    fun array(): ByteArray = storage.copyOf()
    override fun equals(other: Any?): Boolean = other is Bytes && storage.contentEquals(other.storage)
    override fun hashCode(): Int = storage.contentHashCode()
    override fun toString(): String = storage.joinToString(prefix = "[", postfix = "]") { (it.toInt() and 255).toString() }
}

internal enum class NodeKind { COLUMN, ROW, TEXT, BUTTON, INPUT, SCROLL, CANVAS }
internal enum class TouchPhase { DOWN, MOVE, UP, CANCEL }
internal enum class Alignment { START, CENTER, FINISH }
internal data class Point(val x: BigInteger, val y: BigInteger)
internal data class Contact(val id: BigInteger, val point: Point)
internal data class TouchFrame(val phase: TouchPhase, val changed: BigInteger, val milliseconds: BigInteger, val contacts: List<Contact>)

internal sealed interface Input {
    data object Click : Input
    data class Text(val value: String) : Input
    data class Touch(val value: TouchFrame) : Input
    data class Key(val code: BigInteger, val down: Boolean) : Input
    data class Resize(val width: BigInteger, val height: BigInteger, val density: BigInteger) : Input
}

internal sealed interface Reply {
    data class Ok(val value: Bytes) : Reply
    data class Error(val message: String) : Reply
}

internal sealed interface Event {
    data class Node(val revision: BigInteger, val id: BigInteger, val input: Input) : Event
    data class Answer(val id: BigInteger, val reply: Reply) : Event
    data class Subscription(val generation: BigInteger, val id: BigInteger, val payload: Bytes) : Event
    data class Lifecycle(val active: Boolean) : Event
    data object Save : Event
}

internal sealed interface Source {
    data class Tick(val milliseconds: BigInteger) : Source
    data object Back : Source
    data object Pause : Source
    data object Resume : Source
}

internal sealed interface Effect {
    data class Delay(val milliseconds: BigInteger) : Effect
    data class Read(val key: String) : Effect
    data class Write(val key: String, val value: Bytes) : Effect
    data class Log(val text: String) : Effect
    data object Haptic : Effect
    data class Clipboard(val text: String) : Effect
    data class Platform(val name: String, val payload: Bytes) : Effect
}

internal data class Command(val id: BigInteger, val effect: Effect)
internal data class Subscription(val id: BigInteger, val generation: BigInteger, val source: Source)

internal sealed interface Dimension {
    data object Wrap : Dimension
    data object Fill : Dimension
    data class Dp(val value: BigInteger) : Dimension
}

internal sealed interface Draw {
    data class Clear(val color: Long) : Draw
    data class Rect(val origin: Point, val width: BigInteger, val height: BigInteger, val radius: BigInteger, val color: Long) : Draw
    data class Circle(val center: Point, val radius: BigInteger, val color: Long) : Draw
    data class Line(val start: Point, val finish: Point, val width: BigInteger, val color: Long) : Draw
    data class Polygon(val points: List<Point>, val color: Long) : Draw
    data class Text(val origin: Point, val size: BigInteger, val value: String, val color: Long) : Draw
}

internal data class ListenerMask(val click: Boolean, val text: Boolean, val touch: Boolean, val key: Boolean, val resize: Boolean)

internal sealed interface Property {
    data class Text(val value: String) : Property
    data class Hint(val value: String) : Property
    data class Foreground(val value: Long) : Property
    data class Background(val value: Long) : Property
    data class Width(val value: Dimension) : Property
    data class Height(val value: Dimension) : Property
    data class Padding(val value: BigInteger) : Property
    data class Weight(val value: BigInteger) : Property
    data class TextSize(val value: BigInteger) : Property
    data class Enabled(val value: Boolean) : Property
    data class Description(val value: String) : Property
    data class Align(val value: Alignment) : Property
    data class Drawing(val value: List<Draw>) : Property
    data class Listeners(val value: ListenerMask) : Property
}

internal sealed interface Patch {
    data class Create(val id: BigInteger, val kind: NodeKind) : Patch
    data class SetProperty(val id: BigInteger, val value: Property) : Patch
    data class Insert(val parent: BigInteger, val index: BigInteger, val child: BigInteger) : Patch
    data class Remove(val id: BigInteger) : Patch
    data class Root(val id: BigInteger?) : Patch
}

internal sealed interface SubscriptionChange {
    data class Add(val value: Subscription) : SubscriptionChange
    data class Remove(val id: BigInteger, val generation: BigInteger) : SubscriptionChange
}

internal data class Output(val revision: BigInteger, val patches: List<Patch>, val commands: List<Command>, val subscriptions: List<SubscriptionChange>, val snapshot: Bytes?)

internal sealed interface Out {
    data class Changes(val value: Output) : Out
    data class Ignored(val diagnostic: String?) : Out
    data class Failed(val message: String) : Out
}
