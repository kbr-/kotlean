// no_python: This JVM control exercises the actual native ABI and byte-array transport.
package io.kotlean;

import java.util.Arrays;

public final class WireNative {
    private static native boolean matchesEvent(long seed, byte[] bytes);
    private static native boolean matchesInit(long seed, byte[] bytes);
    private static native byte[] output(long seed);
    private static native boolean acceptsOut(byte[] bytes);
    private static native boolean acceptsEvent(byte[] bytes);
    private static native byte[] echo(byte[] bytes);
    private static native byte[] leakingEcho(byte[] bytes);
    private static native String allocatorStats();

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }

    public static void main(String[] args) {
        if (args.length < 1 || args.length > 2) throw new IllegalArgumentException("Expected native library path [stress|leak]");
        System.load(args[0]);
        if (args.length == 2) {
            byte[] bytes = new byte[8192];
            Arrays.fill(bytes, (byte) 37);
            for (int i = 0; i < 10000; i++) require(Arrays.equals(echo(bytes), bytes), "warmup");
            System.out.println("ALLOCATOR WARM " + args[1] + "\n" + allocatorStats());
            for (int phase = 1; phase <= 2; phase++) {
                for (int i = 0; i < 50000; i++) {
                    byte[] result = args[1].equals("leak") ? leakingEcho(bytes) : echo(bytes);
                    require(Arrays.equals(result, bytes), "stress bytes");
                }
                System.out.println("ALLOCATOR PHASE " + phase + " " + args[1] + "\n" + allocatorStats());
            }
            return;
        }
        require(matchesEvent(4, new byte[]{4, 0}), "valid save event rejected");
        require(acceptsEvent(new byte[]{4, 0}), "valid event grammar rejected");
        require(!acceptsEvent(new byte[]{-1, 0}), "invalid event grammar accepted");
        require(!matchesEvent(0, new byte[]{4, 0}), "wrong semantic event accepted");
        require(matchesInit(0, new byte[]{0}), "valid absent snapshot rejected");
        require(!matchesInit(0, new byte[]{2}), "invalid snapshot tag accepted");
        require(!acceptsOut(new byte[]{-1, 0}), "invalid output tag accepted");
        for (long seed : new long[]{0, 1, 2, 3, 255, Long.MIN_VALUE, Long.MAX_VALUE, -1}) {
            byte[] value = output(seed);
            require(value.length != 0, "empty native fixture");
            require(acceptsOut(value), "native fixture rejected");
            require(!acceptsOut(Arrays.copyOf(value, value.length + 1)), "trailing byte accepted");
        }
        for (int size : new int[]{0, 1, 2, 127, 128, 255, 256, 4096}) {
            byte[] value = new byte[size];
            for (int i = 0; i < size; i++) value[i] = (byte) (i * 37);
            byte[] original = value.clone();
            require(Arrays.equals(echo(value), original), "JNI changed output bytes");
            require(Arrays.equals(value, original), "JNI changed input bytes");
        }
        System.out.println("Real JNI positive/negative semantic controls and byte transport passed");
    }
}
