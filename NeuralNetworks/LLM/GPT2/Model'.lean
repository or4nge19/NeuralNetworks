import NeuralNetworks.LLM.GPT2.Core
import NeuralNetworks.LLM.GPT2.TensorView.Lemmas

namespace LLM.GPT2

set_option linter.dupNamespace false

-- = Section 4: GPT-2 Structures ==

structure Config where
  maxSeqLen : Nat       := 1024
  vocabSize : Nat       := 50257
  paddedVocabSize : Nat := 50304
  numLayers : Nat       := 12
  numHeads : Nat        := 12
  channels : Nat        := 768
  deriving Repr, Inhabited

structure ParameterTensors (s : Type) where
  wte : TensorView s
  wpe : TensorView s
  -- Repeating structure for each layer
  ln1w : Array (TensorView s) -- Size numLayers
  ln1b : Array (TensorView s)
  qkvw : Array (TensorView s)
  qkvb : Array (TensorView s)
  attprojw : Array (TensorView s)
  attprojb : Array (TensorView s)
  ln2w : Array (TensorView s)
  ln2b : Array (TensorView s)
  fcw : Array (TensorView s)
  fcb : Array (TensorView s)
  fcprojw : Array (TensorView s)
  fcprojb : Array (TensorView s)
  -- Final layer norm
  lnfw : TensorView s
  lnfb : TensorView s
  -- No deriving Repr for now due to Arrays of TensorViews, can be added later if needed.

structure ActivationTensors (s : Type) where
  encoded : TensorView s
  ln1 : TensorView s
  ln1Mean : TensorView s
  ln1Rstd : TensorView s
  qkv : TensorView s
  attWeights : TensorView s
  attproj : TensorView s
  residual2 : TensorView s
  ln2 : TensorView s
  ln2Mean : TensorView s
  ln2Rstd : TensorView s
  fch : TensorView s
  fchGelu : TensorView s
  fcproj : TensorView s
  residual3 : TensorView s
  lnf : TensorView s
  lnfMean : TensorView s
  lnfRstd : TensorView s
  logits : TensorView s
  probs : TensorView s
  losses : TensorView s
  deriving Repr

structure GPT2 (s : Type) where
  config : Config
  paramsMemoryRef : ST.Ref s ByteArray
  gradsMemoryRef : ST.Ref s ByteArray
  actsMemoryRef : ST.Ref s ByteArray
  gradsActsMemoryRef : ST.Ref s ByteArray
  mMemoryRef : ST.Ref s ByteArray
  vMemoryRef : ST.Ref s ByteArray
  params : ParameterTensors s
  grads : ParameterTensors s
  acts : ActivationTensors s
  gradsActs : ActivationTensors s
  numParameters : Nat
  numActivations : Nat
  -- No deriving Repr for GPT2 if ParameterTensors doesn't have it.

end LLM.GPT2
