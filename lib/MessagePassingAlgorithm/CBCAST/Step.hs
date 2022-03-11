{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- | A single definition about which we will be able to prove properties and
-- say "CBCAST has these properties".
module MessagePassingAlgorithm.CBCAST.Step where

import Redefined
import VectorClock
import MessagePassingAlgorithm.VectorClockAdapter
import MessagePassingAlgorithm.CBCAST




data Input r
    = InputReceive Int (M r)
    | InputDeliver Int
    | InputBroadcast Int r
{-@
data Input r
    = InputReceive
        { inputReceiveN::Nat
        , inputReceiveMessage::Msized r {inputReceiveN}
        }
    | InputDeliver
        { inputDeliverN::Nat
        }
    | InputBroadcast
        { inputBroadcastN::Nat
        , inputBroadcastRaw::r
        }
@-}

{-@
inputSize :: Input r -> Nat @-}
inputSize :: Input r -> Int
inputSize (InputReceive n _)   = n
inputSize (InputDeliver n)     = n
inputSize (InputBroadcast n _) = n
{-@ measure inputSize @-}

{-@ type Isized r N = {i:Input r | inputSize i == N} @-}
{-@ type IasP r P = Isized r {len (pVC P)} @-}

{-@ type PasI r I = Psized r {inputSize I} @-}




data Output r
    = OutputReceive Int (P r)
    | OutputDeliver Int (Maybe (M r, P r))
    | OutputBroadcast Int (M r, P r)
{-@
data Output r
    = OutputReceive
        { outputReceiveN::Nat
        , outputReceiveProces::Psized r {outputReceiveN}
        }
    | OutputDeliver
        { outputDeliverN::Nat
        , outputDeliverResult::Maybe (Msized r {outputDeliverN}, Psized r {outputDeliverN})
        }
    | OutputBroadcast
        { outputBroadcastN::Nat
        , outputBroadcastResult::(Msized r {outputBroadcastN}, Psized r {outputBroadcastN})
        }
@-}

{-@
outputSize :: Output r -> Nat @-}
outputSize :: Output r -> Int
outputSize (OutputReceive n _)   = n
outputSize (OutputDeliver n _)   = n
outputSize (OutputBroadcast n _) = n
{-@ measure outputSize @-}

{-@ type Osized r N = {o:Output r | outputSize o == N} @-}



data Command
    = CommandReceive
    | CommandDeliver
    | CommandBroadcast

inputCommand :: Input r -> Command
inputCommand InputReceive{} = CommandReceive
inputCommand InputDeliver{} = CommandDeliver
inputCommand InputBroadcast{} = CommandBroadcast
{-@ measure inputCommand @-}

outputCommand :: Output r -> Command
outputCommand OutputReceive{} = CommandReceive
outputCommand OutputDeliver{} = CommandDeliver
outputCommand OutputBroadcast{} = CommandBroadcast
{-@ measure outputCommand @-}

-- {-@ type OasI r I = {o:Osized r {inputSize I} | inputCommand I == outputCommand o} @-}
{-@ type OasI r I = Osized r {inputSize I} @-}




{-@ step :: i:Input r -> PasI r {i} -> OasI r {i} @-}
step :: Input r -> P r -> Output r
step (InputReceive   n m) p = OutputReceive   n (internalReceive   m p)
step (InputDeliver   n  ) p = OutputDeliver   n (internalDeliver     p)
step (InputBroadcast n r) p = OutputBroadcast n (internalBroadcast r p)
{-@ reflect step @-}
