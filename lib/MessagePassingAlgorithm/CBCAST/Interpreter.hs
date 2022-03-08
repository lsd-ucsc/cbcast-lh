{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- | A single definition about which we will be able to prove properties and
-- say "CBCAST has these properties".
module MessagePassingAlgorithm.CBCAST.Interpreter where

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




data Output r
    = OutputReceive Int
    | OutputDeliver Int (Maybe (M r))
    | OutputBroadcast Int (M r)
{-@
data Output r
    = OutputReceive
        { outputReceiveN::Nat
        }
    | OutputDeliver
        { outputDeliverN::Nat
        , outputDeliverResult::Maybe (Msized r {outputDeliverN})
        }
    | OutputBroadcast
        { outputBroadcastN::Nat
        , outputBroadcastResult::Msized r {outputBroadcastN}
        }
@-}

{-@
outputSize :: Output r -> Nat @-}
outputSize :: Output r -> Int
outputSize (OutputReceive n)   = n
outputSize (OutputDeliver n _)   = n
outputSize (OutputBroadcast n _) = n
{-@ measure outputSize @-}

{-@ type Osized r N = {o:Output r | outputSize o == N} @-}




{-@ type PasI r I = Psized r {inputSize I} @-}
{-@ type OasI r I = Osized r {inputSize I} @-}

{-@
step :: i:Input r -> PasI r {i} -> (OasI r {i}, PasI r {i}) @-}
step :: Input r -> P r -> (Output r, P r)
step (InputReceive n m) p =
    (OutputReceive n, internalReceive m p)
step (InputBroadcast n r) p =
    let (m, p') = internalBroadcast r p in
    (OutputBroadcast n m, p')
step (InputDeliver n) p =
    case internalDeliver p of
        Nothing -> (OutputDeliver n Nothing, p)
        Just (m, p') -> (OutputDeliver n (Just m), p')
{-@ reflect step @-}
