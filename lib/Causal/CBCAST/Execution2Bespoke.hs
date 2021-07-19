{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Execution2Bespoke where

import Language.Haskell.Liquid.ProofCombinators
import Redefined

-- data DAG
--     = DAGnil
--     | DAGcons
--         { gTail :: DAG
--         , gHead :: Set (Fin {gSize gTail})
--         }

-- data Event pid msg
--     = Broadcast pid msg -- Process pid sends message msg to everyone.
--     | Deliver pid msg -- Process pid delivers message msg to itself.

data Execution pid msg
    = ExNil
    | ExBroadcast
        { ebTail :: Execution pid msg
        , ebProcessOrderEvent :: Maybe Fin
        , ebSender :: pid
        , ebMessage :: msg
        }
    | ExDeliver
        { edTail :: Execution pid msg
        , edProcessOrderEvent :: Maybe Fin
        , edBroadcastEvent :: Fin
        , edReceiver :: pid
        }

{-@ measure executionSize @-}
{-@ executionSize :: _ -> Nat @-}
executionSize :: Execution pid msg -> Int
executionSize ExNil = 0
executionSize ExBroadcast{ebTail} = 1 + executionSize ebTail
executionSize ExDeliver{edTail} = 1 + executionSize edTail

{-@ executionTail :: {ex:_ | ex /= ExNil} -> {out:_ | executionSize ex == 1 + executionSize out} @-}
executionTail :: Execution pid msg -> Execution pid msg
executionTail ExBroadcast{ebTail} = ebTail
executionTail ExDeliver{edTail} = edTail

{-@ using (Execution pid msg) as {ex:_ | 0 < executionSize ex <=> ex /= ExNil} @-}

{-@ sizeFinPositive :: ex:_ -> i:Fin {executionSize ex} -> {0 < executionSize ex} @-}
sizeFinPositive :: Execution pid msg -> Fin -> Proof
sizeFinPositive _ _ = ()

--{-@ executionIndex2 :: {ex:_ | ex /= ExNil} -> i:Fin {executionSize ex} -> _ @-}
--executionIndex2 :: Execution pid msg -> Fin -> Execution pid msg
--executionIndex2 ex i
--    | executionSize exTail == i = ex
--    | otherwise = executionIndex2 exTail i
--  where
--    exTail = executionTail ex

-- XXX output is smaller
-- XXX since 0 <= i < {executionSize ex} then ex cannot be ExNil, and the output cannot be ExNil
--
{-@ executionIndex :: ex:_ -> i:Fin {executionSize ex} -> _ @-}
executionIndex :: Execution pid msg -> Fin -> Execution pid msg
executionIndex ex@ExBroadcast{ebTail} i
    | executionSize ebTail == i = ex
    | otherwise = executionIndex ebTail i
executionIndex ex@ExDeliver{edTail} i
    | executionSize edTail == i = ex
    | otherwise = executionIndex edTail i

-- {-@ eventPID :: ex:_ -> i:Fin {executionSize ex} -> pid @-}
-- eventPID :: Execution pid msg -> Fin -> pid
-- eventPID ex i = case executionIndex ex i of
--     ExBroadcast{ebSender} -> ebSender
--     ExDeliver{edReceiver} -> edReceiver

-- [x] Enforce DAG by constraining the Fin of event fields
-- [ ] Enforce Deliver references Broadcast from distinct-process
-- [ ] Enforce Deliver references own-process-event unless there are none
-- [ ] Enforce Broadcast references own-process-event unless there are none
{-@
data Execution [executionSize] pid msg
    = ExNil
    | ExBroadcast
        { ebTail :: Execution pid msg
        , ebProcessOrderEvent :: Maybe (Fin {executionSize ebTail})
        , ebSender :: pid
        , ebMessage :: msg
        }
    | ExDeliver
        { edTail :: Execution pid msg
        , edProcessOrderEvent :: Maybe (Fin {executionSize edTail})
        , edBroadcastEvent :: Fin {executionSize edTail}
        , edReceiver :: pid
        }
@-}
