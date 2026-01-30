# NeuralNetworks

This project contains Lean 4 formalizations of concepts related to neural networks and associated mathematical structures.

### A more up-to-date development of the Hopfield network material is at [https://github.com/mkaratarakis/HopfieldNet](https://github.com/or4nge19/HopfieldNet2) ###

### Project Structure

The repository is organized into several directories, each focusing on a specific area of formalization.

#### `NeuralNetworks/Hopfield/`
This directory contains the formalization of Hopfield networks.
- **Basic.lean**: Defines core structures such as `SpinState`, `HopfieldState`, and `HopfieldNetwork`.
- **BasicComputable.lean**: Provides computable versions of the basic definitions.
- **Energy.lean**: Defines the energy function and includes proofs of its properties, such as monotonic decrease during updates.
- **Convergence.lean**: Contains proofs regarding the convergence of network states to fixed points.
- **Hebbian/**: Implements the Hebbian learning rule for weight matrix construction.
- **Biased.lean**: Extends the `HopfieldNetwork` structure with a bias term.
- **Asymmetric.lean**: Defines asymmetric Hopfield networks and conditions for their convergence.
- **StochasticUpdate.lean**: Formalizes stochastic update rules for the network state.

#### `NeuralNetworks/LLM/`
This directory contains formalizations related to Large Language Models.
- **GPT2/**: A formalization of aspects of the GPT-2 model.
    - `Core.lean`, `Model.lean`, `Model'.lean`: Define the core components and structure of the model.
    - `TensorView/`: A library for tensor-like data structures and operations.
    - `ByteArrayUtils.lean`: Utility functions for byte arrays.

#### `NeuralNetworks/NN/`
This directory contains various formalizations for general neural networks.
- **NN.lean**: General definitions for neural networks.
- **NNQuiver.lean**: A representation of neural networks using quivers.
- **ContinuousDynamics.lean**: Formalization of neural networks as continuous dynamical systems.
- **ProximalGradientNN.lean**: Formalization of proximal gradient methods for training.


#### Other Directories
- **CReals/**: A WIP library for computable real numbers.
- **Float/**: A WIP library for floating-point arithmetic.
- **Optlib/**: A local copy of the Optlib library.

### Getting Started

To use this formalization, Lean 4 must be installed. Clone the repository to access the Lean files.

```sh
git clone <repository-url>
cd NeuralNetworks
```

### Usage

The Lean files are located in the `NeuralNetworks/` directory. Each file can be explored for its specific definitions, theorems, and proofs.

### Contributions

Contributions are welcome. Please fork the repository and submit a pull request for any proposed changes.

### License

This project is licensed under the Apache License.
