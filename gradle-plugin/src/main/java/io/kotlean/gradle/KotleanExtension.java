// no_java: Gradle requires JVM property types for its managed extension.
package io.kotlean.gradle;

import org.gradle.api.file.DirectoryProperty;
import org.gradle.api.provider.Property;

public abstract class KotleanExtension {
    public abstract DirectoryProperty getPackageDirectory();
    public abstract Property<String> getExecutable();
    public abstract Property<String> getModule();
    public abstract Property<String> getLibraryName();
}
