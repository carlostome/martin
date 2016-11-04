# Martin

The interactive Agda tutor system

## Prerequisites

This tutoring system is implemented in the Haskell programming language using the GHC compiler in version 8.0.1.
Furthermore, it relies on the `stack` build system to provide a set of dependencies with compatible versions.

1.  Install GHC 8.0.1 on your computer, for example by dowloading and installing
    the [Haskell Platform](https://www.haskell.org/platform/) for your operating system.
    The three main platforms, Windows, Mac OS X and Linux are supported.

2.  Install the Stack tool. Detailed instructions on the installation can be found [here](https://docs.haskellstack.org/en/stable/README/#how-to-install).

## Building

1.  Clone this repository or extract the source code.

    ```bash
    git clone https://github.com/carlostome/martin.git
    ```

2.  Run `stack build` from a terminal in the project directory.

**NOTE**: We recommend building the project using stack. While it might be possible to compile it using `cabal build`, we cannot guarantee that `cabal` will select compatible versions of the dependencies.

## Usage

Run the program with `stack exec martin-exe` and have fun! 

**NOTE**: When executed through stack, command line options can be passed to the tutoring system by separating them with a double dash from the stack command: `stack exec martin-exe -- <options for martin>`.

To start the interactive terminal application, run it with the `-a` option, passing the file as the last argument.
The command for starting the tutor from the project root directory with the vector example is

```bash
stack exec martin-exe -- -a examples/Vec.agda
```

Alternatively, it is also possible to just generate and print a strategy by passing `-p` instead of `-a`.

Modules imported by the selected Agda file are resolved relative to the current directory in which the application has been executed.
