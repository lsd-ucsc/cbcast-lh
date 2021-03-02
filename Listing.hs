import Data.IORef

import Causal.CBCAST.Process
import Causal.CBCAST.Protocol

-- | Extended example from Fig 4 of the paper (the corrected Alice/Bob/Carol
-- executions).
main :: IO ()
main = do
    leftExample
    putStrLn $ replicate 10 '='
    rightExample


leftExample :: IO ()
leftExample = do
    -- Three causal broadcast processes which send String messages.
    alice <- newIORef (pNew 0 3 :: Process String)
    bob   <- newIORef (pNew 1 3 :: Process String)
    carol <- newIORef (pNew 2 3 :: Process String)

    -- Alice sends 'lost' and their VC increments to [1,0,0].
    -- Alice's message is conveyed by transport.
    modifyIORef alice $ send "I lost my wallet..."
    aliceBcastLost <- atomicModifyIORef alice drainBroadcasts

    -- Bob receives 'lost' and delivers it, updating their VC to [1,0,0].
    modifyIORef bob $ \p -> foldr receive p aliceBcastLost
    Just _lost <- atomicModifyIORef bob deliver -- Message ... "I lost my wallet..."

    -- Alice sends 'found' and their VC increments to [2,0,0].
    -- Alice's message is conveyed by transport.
    modifyIORef alice $ send "Found it!"
    aliceBcastFound <- atomicModifyIORef alice drainBroadcasts

    -- Carol receives 'found' and delays it because it depends on 'lost'.
    modifyIORef carol $ \p -> foldr receive p aliceBcastFound
    Nothing <- atomicModifyIORef carol deliver

--  -- Bob receives 'found' and delivers it, updating their VC to [2,0,0].
--  modifyIORef bob $ \p -> foldr receive p aliceBcastFound
--  Just _found <- atomicModifyIORef bob deliver -- Message ... "Found it!"

    -- Carol receives 'lost' and delivers it, updating their VC to [1,0,0].
    modifyIORef carol $ \p -> foldr receive p aliceBcastLost
    Just _lost <- atomicModifyIORef carol deliver -- Message ... "I lost my wallet..."

    -- Carol delivers 'found', updating their VC to [2,0,0]
    Just found <- atomicModifyIORef carol deliver -- Message ... "Found it!"

    print found


rightExample :: IO ()
rightExample = do
    -- Three causal broadcast processes which send String messages.
    alice <- newIORef (pNew 0 3 :: Process String)
    bob   <- newIORef (pNew 1 3 :: Process String)
    carol <- newIORef (pNew 2 3 :: Process String)

    -- Alice sends 'lost' and their VC increments to [1,0,0].
    -- Alice's message is conveyed by transport.
    modifyIORef alice $ send "I lost my wallet..."
    aliceBcastLost <- atomicModifyIORef alice drainBroadcasts
--  -- Alice delivers their own message and their VC is not changed.
--  Just _lost <- atomicModifyIORef alice deliver -- Message ... "I lost my wallet..."

    -- Bob receives 'lost' and delivers it, updating their VC to [1,0,0].
    modifyIORef bob $ \p -> foldr receive p aliceBcastLost
    Just _lost <- atomicModifyIORef bob deliver -- Message ... "I lost my wallet..."

    -- Alice sends 'found' and their VC increments to [2,0,0].
    -- Alice's message is conveyed by transport.
    modifyIORef alice $ send "Found it!"
    aliceBcastFound <- atomicModifyIORef alice drainBroadcasts
--  -- Alice delivers their own message and their VC is not changed.
--  Just _found <- atomicModifyIORef alice deliver -- Message ... "Found it!"

    -- Bob receives 'found' and delivers it, updating their VC to [2,0,0].
    modifyIORef bob $ \p -> foldr receive p aliceBcastFound
    Just _found <- atomicModifyIORef bob deliver -- Message ... "Found it!"

    -- Carol receives 'lost' and delivers it, updating their VC to [1,0,0].
    modifyIORef carol $ \p -> foldr receive p aliceBcastLost
    Just _lost <- atomicModifyIORef carol deliver -- Message ... "I lost my wallet..."

    -- Bob sends 'glad' and their VC increments to [2,1,0].
    -- Bob's message is conveyed by transport.
    modifyIORef bob $ send "Glad to hear it!"
    bobBcastGlad <- atomicModifyIORef bob drainBroadcasts

--  -- Alice receives 'glad' and delivers it, updating their VC to [2,1,0].
--  modifyIORef alice $ \p -> foldr receive p bobBcastGlad
--  Just _glad <- atomicModifyIORef alice deliver -- Message ... "Glad to hear it!"

    -- Carol receives 'glad' and delays it because it depends on 'found'.
    modifyIORef carol $ \p -> foldr receive p bobBcastGlad
    Nothing <- atomicModifyIORef carol deliver

    -- Carol receives 'found' and delivers it, updating their VC to [2,0,0].
    modifyIORef carol $ \p -> foldr receive p aliceBcastFound
    Just _found <- atomicModifyIORef carol deliver -- Message ... "Found it!"

    -- Carol delivers 'glad', updating their VC to [2,1,0].
    Just glad <- atomicModifyIORef carol deliver -- Message ... "Glad to hear it!"

    print glad
