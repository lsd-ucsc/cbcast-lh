module Causal.Execution.Properties where
-- | Properties of reachable executions

import Causal.Execution.Reachable

-- NOTE: for gomes' we have defn
--      x \sqrsubset^i y
--          iff there exists xs, ys, and zs s.t. xs@[x]@ys@[y]@zs = history i

-- TODO: gomes' histories-distinct property on the node-histories locale

-- Going along with the histories-distinct property below, also prove:
--  * an event in one process-state does not appear in another process-state
--  * NOT-USEFUL the sum of the lengths of process-states in an execution is equal to the size of the events set for the execution
--  * NOT-USEFUL the length of a process-state is equal to the size of the set of events it contains
--  * an event is a process-state does not appear elsewhere in that process-state

-- TODO: gomes' delivery-has-a-cause property on the network locale
--      [[ Deliver m \in set (history i) ]] \implies \exists j. Broadcast m \in set (history j)

-- TODO: gomes' deliver-locally property on the network locale
--      [[ Broadcast m \in set (history i) ]] \implies Broadcast m \sqrsubset^i Deliver m

-- TODO: gomes' msg-id-unique property on the network locale
--      [[ Broadcast m1 \in set (history i);
--         Broadcast m2 \in set (history j);
--         msg-id m1 = msg-id m2 ]] \implies i = j \land m1 = m2

-- XXX what about properties for the eventOrder or happensBefore relation?
