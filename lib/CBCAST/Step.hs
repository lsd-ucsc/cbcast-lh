{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- | Single CBCAST transition stepper.
module CBCAST.Step where

import VectorClock
import CBCAST.Core
import CBCAST.Transitions




-- * Transition input

data Op r
    = OpReceive Int (Message r)
    | OpDeliver Int
    | OpBroadcast Int r
{-@
data Op r
    = OpReceive
        { opReceiveN::Nat
        , opReceiveMessage::Msized r {opReceiveN}
        }
    | OpDeliver
        { opDeliverN::Nat
        }
    | OpBroadcast
        { opBroadcastN::Nat
        , opBroadcastRaw::r
        }
@-}

opSize :: Op r -> Int
opSize (OpReceive n _)   = n
opSize (OpDeliver n)     = n
opSize (OpBroadcast n _) = n
{-@ measure opSize @-}
{-# WARNING opSize "Verification only" #-}

{-@ type OPsized r N = {op:Op r | opSize op == N} @-}
{-@ type OPasP r P = OPsized r {processSize P} @-}




-- * Transition output

data Result r
    = ResultReceive Int (Process r)
    | ResultDeliver Int (Maybe (Message r, Process r))
    | ResultBroadcast Int (Message r, Process r)
{-@
data Result r
    = ResultReceive
        { resultReceiveN::Nat
        , resultReceiveProces::Psized r {resultReceiveN}
        }
    | ResultDeliver
        { resultDeliverN::Nat
        , resultDeliverResult::Maybe (Msized r {resultDeliverN}, Psized r {resultDeliverN})
        }
    | ResultBroadcast
        { resultBroadcastN::Nat
        , resultBroadcastResult::(Msized r {resultBroadcastN}, Psized r {resultBroadcastN})
        }
@-}

resultSize :: Result r -> Int
resultSize (ResultReceive n _)   = n
resultSize (ResultDeliver n _)   = n
resultSize (ResultBroadcast n _) = n
{-@ measure resultSize @-}
{-# WARNING resultSize "Verification only" #-}

{-@ type RETsized r N = {ret:Result r | resultSize ret == N} @-}
{-@ type RETasOP r OP = RETsized r {opSize OP} @-}

data Command
    = CommandReceive
    | CommandDeliver
    | CommandBroadcast

opCommand :: Op r -> Command
opCommand OpReceive{} = CommandReceive
opCommand OpDeliver{} = CommandDeliver
opCommand OpBroadcast{} = CommandBroadcast
{-@ measure opCommand @-}
{-# WARNING opCommand "Verification only" #-}

resultCommand :: Result r -> Command
resultCommand ResultReceive{} = CommandReceive
resultCommand ResultDeliver{} = CommandDeliver
resultCommand ResultBroadcast{} = CommandBroadcast
{-@ measure resultCommand @-}
{-# WARNING resultCommand "Verification only" #-}

{-@ type RETasOPcmd r OP = {ret:RETasOP r {OP} | opCommand OP == resultCommand ret} @-}




{-@ type PasOP r OP = Psized r {opSize OP} @-}

{-@ step :: op:Op r -> PasOP r {op} -> RETasOPcmd r {op} @-}
step :: Op r -> Process r -> Result r
step (OpReceive   n m) p = ResultReceive   n (internalReceive   m p)
step (OpDeliver   n  ) p = ResultDeliver   n (internalDeliver     p)
step (OpBroadcast n r) p = ResultBroadcast n (internalBroadcast r p)
{-@ reflect step @-}
