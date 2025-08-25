# Zephyr Model-Based Testing

This repository contains PlusCal specifications of Zephyr RTOS kernel APIs.
Currently, this includes the semaphore API and the mutex API.

## Model-Based Testing

The specifications were created in order to perform Model-Based Testing (MBT) of the APIs.
For MBT, the model-checker TLC2 is used to generate traces from the models.
These traces are then translated to runnable ZTEST test cases.

The translation happens in part by using the `ALIAS` feature of TLC,
which can be used to reformat counterexample states.
In our case, we use an `ALIAS` to add C instructions to the counterexamples,
which should be executed in the resulting test case.

A python tool, which generates the final, runnable ZTEST file from the traces will be added to this repository soon.

## System Requirements

In order to work with the specifications, you need to have the [TLA+ Toolbox](https://github.com/tlaplus/tlaplus) installed, which requires  Java 11+.
You can either install these requirements on your system or (recommended) open this project in VSCode and use the provided devcontainer config.

If you choose to install the toolbox yourself, you should have a Java archive `tla2tools.jar` somewhere on your file system.
The remainder of this README assumes that the environment variable `$TLA_TOOLS_JAR` contains the path to that archive.
The devcontainer sets this variable automatically.

### pre-commit

We use `pre-commit` to remove generated PlusCal translations from the tla-files.
The devcontainer already includes `pre-commit`.
If you are not using the devcontainer, please install `pre-commit` on your system and
set it up for this repository by running `pre-commit install`.

## Working with the Specifications

In order to check a specification (e.g. `Semaphores.tla`), navigate to the containing directory.

```bash
cd specs/semaphores
```

### Translate the PlusCal spec to TLA+

Since the specifications are written in PlusCal, you need to translate them to TLA+ using the PlusCal
translator included in the TLA+ tools:

```
java -cp $TLA_TOOLS_JAR pcal.trans Semaphores.tla
```

This will generate the necessary TLA+ specification and write it into the same file.

### Run TLC2 on the TLA+ Spec

Next, run the model checker on the specification.
Since the mutex and semaphore specifications use common TLA+ modules stored in `specs/lib`,
we need to set the system property `DTLA-Library` to `../lib` in the java runtime.
Note that this only works if running directly from the directory that contains the specification `Semaphores.tla`.

```
java -DTLA-Library=../lib -jar $TLA_TOOLS_JAR Semaphores.tla
```

The model checker will then check the model and search for errors, deadlocks, and property violations.
For the above invocation, no errors should be reported.

### Model Checker Configuration and Trace Generation

When running the model checker, it requires a `*.cfg` file,
which assigns values to model parameters and tells the model checker which properties to check.
If no config file is passed explicitly, TLC2 will use the configuration with the same basename as the spec
(e.g. `Semaphores.cfg` for `Semaphores.tla`).

In order to generate a trace from a model, we need to configure the model checker to
check a property which is not true (a *trap property*).
Such properties are already defined in the specifications and only need to be activated using the correct
configuration:

If you check the model again with the `SemaphoresMBT.cfg` configuration, the model checker should output
a trace, as it finds a property violation:

```
java -DTLA-Library=../lib -jar $TLA_TOOLS_JAR -config SemaphoresMBT.cfg Semaphores.tla
```

### Specification Structure

The specifications are composed of multiple TLA+ module.
The structure of the Semaphore specification is given here.
The mutex specification is structured in the same way.
More detailed information on each module is given as comments in the module.

- `Semaphores.tla`: This module contains the PlusCal specification,
  including the specification of API functions. This specification
  references the remaining TLA+ modules.
- `SemaphoreInvariants.tla`: Contains invariants that must hold for
  the semaphore specification.
- `SemaphoreTrapProperties.tla`: Contains invariants or action properties
  that are **not** true. Checking these with TLC results in counterexamples.
- `SemaphoreTestGen.tla`: Contains translation information for generating
  a ZTEST test case. This includes C variable definitions and translations
  of PlusCal labels to corresponding C instructions.

In addition, there are two configs for the specification:

- `Semaphores.cfg`: The regular config, only used for verification of invariants
  that we expect to be true.
- `SemaphoresMBT.cfg`: This config specifies Trap Properties to be checked, which
  will cause TLC to produce counterexamples. It also configures the `ALIAS` used
  for C code generation.
