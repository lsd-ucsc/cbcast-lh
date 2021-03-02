-- | Extended example from Fig 4 of the paper (the corrected Alice/Bob/Carol
-- executions).
module Main where

import Data.IORef

import Causal.CBCAST.Process
import Causal.CBCAST.Protocol


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
    Just message <- atomicModifyIORef bob deliver -- Message ... "I lost my wallet..."
    print message

    -- Alice sends 'found' and their VC increments to [2,0,0].
    -- Alice's message is conveyed by transport.
    modifyIORef alice $ send "Found it!"
    aliceBcastFound <- atomicModifyIORef alice drainBroadcasts

    -- Carol receives 'found' and delays it because it depends on 'lost'.
    modifyIORef carol $ \p -> foldr receive p aliceBcastFound
    Nothing <- atomicModifyIORef carol deliver

    -- Bob receives 'found' and delivers it, updating their VC to [2,0,0].
    modifyIORef bob $ \p -> foldr receive p aliceBcastFound
    Just message <- atomicModifyIORef bob deliver -- Message ... "Found it!"
    print message

    -- Carol receives 'lost' and delivers it, updating their VC to [1,0,0].
    modifyIORef carol $ \p -> foldr receive p aliceBcastLost
    Just message <- atomicModifyIORef carol deliver -- Message ... "I lost my wallet..."
    print message

    -- Carol delivers 'found', updating their VC to [2,0,0]
    Just message <- atomicModifyIORef carol deliver -- Message ... "Found it!"
    print message


rightExample :: IO ()
rightExample = do
    -- Three causal broadcast processes which send String messages.
    alice <- newIORef (pNew 0 3 :: Process String)
    bob   <- newIORef (pNew 1 3 :: Process String)
    carol <- newIORef (pNew 2 3 :: Process String)

    -- Alice sends 'lost' and their VC increments to [1,0,0].
    -- Alice's message is conveyed by transport.
    -- Alice delivers their own message and their VC is not changed.
    modifyIORef alice $ send "I lost my wallet..."
    aliceBcastLost <- atomicModifyIORef alice drainBroadcasts
    Just message <- atomicModifyIORef alice deliver -- Message ... "I lost my wallet..."
    print message

    -- Bob receives 'lost' and delivers it, updating their VC to [1,0,0].
    modifyIORef bob $ \p -> foldr receive p aliceBcastLost
    Just message <- atomicModifyIORef bob deliver -- Message ... "I lost my wallet..."
    print message

    -- Alice sends 'found' and their VC increments to [2,0,0].
    -- Alice's message is conveyed by transport.
    -- Alice delivers their own message and their VC is not changed.
    modifyIORef alice $ send "Found it!"
    aliceBcastFound <- atomicModifyIORef alice drainBroadcasts
    Just message <- atomicModifyIORef alice deliver -- Message ... "Found it!"
    print message

    -- Bob receives 'found' and delivers it, updating their VC to [2,0,0].
    modifyIORef bob $ \p -> foldr receive p aliceBcastFound
    Just message <- atomicModifyIORef bob deliver -- Message ... "Found it!"
    print message

    -- Carol receives 'lost' and delivers it, updating their VC to [1,0,0].
    modifyIORef carol $ \p -> foldr receive p aliceBcastLost
    Just message <- atomicModifyIORef carol deliver -- Message ... "I lost my wallet..."
    print message

    -- Bob sends 'glad' and their VC increments to [2,1,0].
    -- Bob's message is conveyed by transport.
    modifyIORef bob $ send "Glad to hear it!"
    bobBcastGlad <- atomicModifyIORef bob drainBroadcasts

    -- Alice receives 'glad' and delivers it, updating their VC to [2,1,0].
    modifyIORef alice $ \p -> foldr receive p bobBcastGlad
    Just message <- atomicModifyIORef alice deliver -- Message ... "Glad to hear it!"
    print message

    -- Carol receives 'glad' and delays it because it depends on 'found'.
    modifyIORef carol $ \p -> foldr receive p bobBcastGlad
    Nothing <- atomicModifyIORef carol deliver

    -- Carol receives 'found' and delivers it, updating their VC to [2,0,0].
    modifyIORef carol $ \p -> foldr receive p aliceBcastFound
    Just message <- atomicModifyIORef carol deliver -- Message ... "Found it!"
    print message

    -- Carol delivers 'glad', updating their VC to [2,1,0].
    Just message <- atomicModifyIORef carol deliver
    print message
