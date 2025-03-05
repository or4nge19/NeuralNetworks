# NeuralNetworks

## Hopfield Networks Formalization

This project contains a Lean 4 formalization of Hopfield networks. Hopfield networks are a type of recurrent artificial neural network that serve as content-addressable memory systems. This repository includes implementations and proofs for various concepts and features of Hopfield networks.

### Features

- **SpinState**: Represents a binary spin, either up or down, and supports conversion to real numbers, Boolean values, and ZMod 2.
- **HopfieldState**: Represents the state of a Hopfield network with `n` neurons.
- **MetricSpace**: Endows `HopfieldState` with the Hamming distance.
- **HopfieldNetwork**: Consists of a real-valued weight matrix and a threshold vector, with functions for energy calculation, local field computation, and state updates.
- **UpdateSeq**: Represents a sequence of asynchronous updates on the Hopfield network.
- **Fixed Points and Convergence**: Defines fixed points and convergence criteria for states in the network.
- **ContentAddressableMemory**: Wraps a Hopfield network and a set of stored patterns, providing a threshold criterion for pattern completion.
- **BiasedHopfieldNetwork**: Extends `HopfieldNetwork` by adding a bias term to the local field.
- **EnergyDecrease**: Proves that the energy function for a Hopfield network decreases monotonically with each spin update.
- **DifferentUpdateRules**: Provides various update rules such as synchronous and stochastic updates.

### Getting Started

To use this formalization, you need to have Lean 4 installed on your system. Clone this repository and explore the `HopfieldNetworks` directory for the Lean files and their respective formalizations.

### Usage

The main file for the Hopfield networks formalization is `HopfieldNetworks/Basic.lean`. It includes all the definitions, structures, and proofs related to Hopfield networks. Additionally, you can find energy-related proofs in `HopfieldNetworks/Energy.lean`, and biased network extensions in `HopfieldNetworks/Biased.lean`.

### Contributions

Contributions are welcome! If you have any improvements or new features to add, feel free to fork the repository and create a pull request.

### License

This project is licensed under the Apache License.
