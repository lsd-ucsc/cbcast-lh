
-- | A single definition about which we will be able to prove properties and
-- say "CBCAST has these properties".
module MessagePassingAlgorithm.CBCAST.Interpreter where

import Redefined
import VectorClock
import MessagePassingAlgorithm.VectorClockAdapter
import MessagePassingAlgorithm.CBCAST

data Input r
    = InputReceive (M r) (P r)
    | InputDeliver (P r)
    | InputBroadcast r (P r)
{-@
data Input r
    = InputReceive
        { inputReceiveMessage::M r
        , inputReceiveProcess::PasM r {inputReceiveMessage}
        }
    | InputDeliver
        { inputDeliverProcess::P r
        }
    | InputBroadcast
        { inputBroadcastRaw::r
        , inputBroadcastProcess::P r
        }
@-}

-- What about output sizes?
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
pSize :: P r -> Nat @-}
pSize :: P r -> Int
pSize p = listLength (pVC p)
{-@ inline pSize @-}

-- {-@ ple interpret @-}
interpret :: Input r -> Output r
interpret (InputReceive m p)    = OutputReceive (pSize p) (internalReceive m p)
interpret (InputDeliver p)      = OutputDeliver (pSize p) (internalDeliver p)
interpret (InputBroadcast r p)  = OutputBroadcast (pSize p) (internalBroadcast r p)
{-@ reflect interpret @-}
