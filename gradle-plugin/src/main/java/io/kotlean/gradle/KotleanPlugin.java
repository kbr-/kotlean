// no_java: Gradle and AGP expose JVM APIs; dependency discovery and compilation stay in Lean.
package io.kotlean.gradle;

import com.android.build.api.variant.ApplicationAndroidComponentsExtension;
import java.io.File;
import java.util.Arrays;
import kotlin.Unit;
import org.gradle.api.GradleException;
import org.gradle.api.Plugin;
import org.gradle.api.Project;

public final class KotleanPlugin implements Plugin<Project> {
    @Override
    public void apply(Project project) {
        var extension = project.getExtensions().create("kotlean", KotleanExtension.class);
        extension.getPackageDirectory().convention(project.getLayout().getProjectDirectory().dir("lean"));
        extension.getExecutable().convention(project.getProviders().environmentVariable("KOTLEAN_BUILD").orElse("kotlean"));
        extension.getModule().convention("auto");
        extension.getLibraryName().convention(project.getName());
        var inputText = extension.getExecutable().flatMap(executable ->
            extension.getPackageDirectory().flatMap(directory -> extension.getModule().flatMap(module -> {
                var process = project.getProviders().exec(spec -> {
                    spec.setIgnoreExitValue(true);
                    spec.commandLine(executable, "inputs", directory.getAsFile().getAbsolutePath(), module);
                });
                return process.getResult().map(result -> {
                    if (result.getExitValue() != 0) {
                        throw new GradleException("Kotlean input discovery failed:\n" + process.getStandardError().getAsText().get());
                    }
                    return process.getStandardOutput().getAsText().get();
                });
            })));
        var inputs = inputText.map(paths -> Arrays.stream(paths.split(String.valueOf((char) 0)))
            .filter(path -> !path.isEmpty()).map(File::new).toList());
        var task = project.getTasks().register("buildKotlean", BuildKotlean.class, build -> {
            build.getPackageDirectory().set(extension.getPackageDirectory());
            build.getExecutable().set(extension.getExecutable());
            build.getModule().set(extension.getModule());
            build.getLibraryName().set(extension.getLibraryName());
            build.getSourceFiles().from(inputs);
            build.getOutputDirectory().set(project.getLayout().getBuildDirectory().dir("generated/kotlean/jniLibs"));
        });
        project.getPluginManager().withPlugin("com.android.application", ignored -> {
            var android = project.getExtensions().getByType(ApplicationAndroidComponentsExtension.class);
            android.onVariants(android.selector().all(), variant -> {
                var libraries = variant.getSources().getJniLibs();
                if (libraries != null) libraries.addGeneratedSourceDirectory(task, BuildKotlean::getOutputDirectory);
                return Unit.INSTANCE;
            });
        });
    }
}
