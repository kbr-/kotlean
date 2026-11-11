// no_python: Gradle task execution uses its JVM I/O API and delegates compilation to Lean.
package io.kotlean.gradle;

import java.io.File;
import javax.inject.Inject;
import org.gradle.api.DefaultTask;
import org.gradle.api.file.ConfigurableFileCollection;
import org.gradle.api.file.DirectoryProperty;
import org.gradle.api.file.FileSystemOperations;
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
    private final FileSystemOperations files;

    @Inject
    public BuildKotlean(ExecOperations processes, FileSystemOperations files) {
        this.processes = processes;
        this.files = files;
    }

    @Internal public abstract DirectoryProperty getPackageDirectory();
    @Input public abstract Property<String> getExecutable();
    @Input public abstract Property<String> getModule();
    @Input public abstract Property<String> getLibraryName();
    @InputFiles @PathSensitive(PathSensitivity.RELATIVE)
    public abstract ConfigurableFileCollection getSourceFiles();
    @OutputDirectory public abstract DirectoryProperty getOutputDirectory();

    @TaskAction
    public void build() {
        var library = new File(getTemporaryDir(), "lib" + getLibraryName().get() + ".so");
        processes.exec(spec -> spec.commandLine(
            getExecutable().get(), "build", getPackageDirectory().get().getAsFile().getAbsolutePath(),
            getModule().get(), library.getAbsolutePath()
        )).assertNormalExitValue();
        files.sync(spec -> {
            spec.into(getOutputDirectory());
            spec.from(library, arm64 -> arm64.into("arm64-v8a"));
        });
    }
}
