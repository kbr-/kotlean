// no_python: Gradle task execution uses its JVM I/O API and delegates compilation to Lean.
package io.kotlean.gradle;

import javax.inject.Inject;
import org.gradle.api.DefaultTask;
import org.gradle.api.file.ConfigurableFileCollection;
import org.gradle.api.file.DirectoryProperty;
import org.gradle.api.provider.Property;
import org.gradle.api.tasks.Input;
import org.gradle.api.tasks.InputFiles;
import org.gradle.api.tasks.Internal;
import org.gradle.api.tasks.OutputDirectory;
import org.gradle.api.tasks.PathSensitive;
import org.gradle.api.tasks.PathSensitivity;
import org.gradle.api.tasks.TaskAction;
import org.gradle.process.ExecOperations;

public abstract class BuildKotlean extends DefaultTask {
    private final ExecOperations processes;

    @Inject
    public BuildKotlean(ExecOperations processes) { this.processes = processes; }

    @Internal public abstract DirectoryProperty getPackageDirectory();
    @Input public abstract Property<String> getExecutable();
    @Input public abstract Property<String> getModule();
    @Input public abstract Property<String> getLibraryName();
    @InputFiles @PathSensitive(PathSensitivity.RELATIVE)
    public abstract ConfigurableFileCollection getSourceFiles();
    @OutputDirectory public abstract DirectoryProperty getOutputDirectory();

    @TaskAction
    public void build() {
        processes.exec(spec -> spec.commandLine(
            getExecutable().get(), "build", getPackageDirectory().get().getAsFile().getAbsolutePath(),
            getModule().get(), getOutputDirectory().file("arm64-v8a/lib" + getLibraryName().get() + ".so")
                .get().getAsFile().getAbsolutePath()
        )).assertNormalExitValue();
    }
}
