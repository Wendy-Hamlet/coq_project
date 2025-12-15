# QCP: A Practical Separation Logic-based C Program Verification Tool

## File Structure
- `linux-binary/`, `win-binary/`: Precompiled QCP binaries
- `QCP_examples/`: Annotated C programs
- `SeparationLogic/`: Rocq scripts to check QCP-generated VCs
- `tutorial/`: Step-by-step QCP usage guide
- `run-example-linux.sh`, `run-example-windows.sh`: Scripts to run QCP examples
- `qide.vsix` : QCP VSCode Extension

## Environment Setup

### Prerequisites

- Docker installed ([Get Docker](https://docs.docker.com/get-docker/))
- Visual Studio Code ([Download](https://code.visualstudio.com/))
- VS Code Remote - Containers extension ([Install](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers))

### Build the Docker Image

Open a terminal in the project root and run:

```sh
docker build --build-arg MAKE_JOBS=5 -t qcp .
```

This will build the Docker image using the provided `Dockerfile`.

### Run VS Code Devcontainer

1. Check the `.devcontainer/devcontainer.json` file exists in the project root.
2. Open the project root folder in VS Code.
3. When prompted, click "Reopen in Container" or use the command palette:
   - `Ctrl+Shift+P` → "Dev Containers: Reopen in Container"
4. VS Code will build the container and set up the environment automatically.

## QIDE Extension

### Setup

The QIDE extension for VS Code should be automatically installed and configured when using the devcontainer setup. If not, follow these steps:

- Install the QIDE extension from the VS Code UI.
  (Note that we did not publish the extension to the marketplace, so do not search for it in the extensions shop.)
  - Open the command palette (`Ctrl+Shift+P`)
  - Select "Extensions: Install from VSIX..."
  - Choose the VSIX file `qide.vsix` from the project root.
- QIDE extension settings: open `File > Preferences > Settings`, search for `qide`, and set:
  - `qide.lspBinPath` to the path of the QCP binary (e.g., `linux-binary/lsp`)
  - `qide.lspArg` is the excution options for QCP. You can leave it empty refer to `Options to run QCP`.

### Usage

- Open an annotated C program.
- Move the cursor to any place you like and press `Alt+Rightarrow`.
  You can change the keyboard shortcuts settings if needed.
  You can also run the command `qide.interpretToPoint` directly from the command palette (`Ctrl+Shift+P`).

### QCP Command-Line Tool

The `run-example-linux.sh` and `run-example-windows.sh` scripts in the root directory give examples of how to run QCP command-line tool. You can directly execute them if you have the required environment set up.

Below is a summary of the main command-line options of QCP. We also recommend following the tutorials in the `tutorial/` folder for a comprehensive guide.

**Usage:**
```
linux_binary/symexec [options]
```

**Required options:**
- `--input-file=<file>`: Specify the input C source code.
- `--goal-file=<file>`: Output file for generated verification conditions (VCs).
- `--proof-auto-file=<file>`: Output file for automatically solved VCs.
- `--proof-manual-file=<file>`: Output file for VCs requiring manual proofs.

**Optional flags:**
- `--gen-and-backup`: If output files exist, back them up before overwriting; otherwise, only "proof-manual" is backed up.
- `--no-exec-info`: Suppress intermediate information during symbolic execution.
- `--coq-logic-path=<path>`: Specify the Coq logic path for the goal file.
- `-slp <dir> <path>`: Add a directory to the strategy search paths.
- `-I<dir>`: Add a directory to the include search paths.

**Preprocessing:**
If your C source uses preprocessor directives (`#define`, `#include`, etc.), preprocess it first:
```
cpp -C <input-file> <output-file>
```
Note: Only `#include` is natively supported.

**Coq Integration:**
The generated `.v` files must be used with SeparationLogic. For details, see `SeparationLogic/README.md`.


## Evaluation

Our evaluation consists of two parts: the Tool component and the VSCode Extension component. 
- The Tool component allows you to check files in the ``QCP_examples`` by running ``sh ./run-example-linux.sh``, and it generates the corresponding Coq files in the ``SeparationLogic/examples/`` directory. 
- The VSCode Extension component is designed to support real-time verification interaction. You can open any annotated C file to view the current assertion state, which facilitates the continued writing of annotations for proofs.