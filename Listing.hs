-- | Extended example from Fig 4 of the paper (the corrected Alice/Bob/Carol
-- executions).

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
    alice <- newIORef (pNew 0 3 :: Process String)
    bob   <- newIORef (pNew 1 3 :: Process String)
    carol <- newIORef (pNew 2 3 :: Process String)

    putStrLn "Alice sends 'lost'"
    modifyIORef alice $ send "I lost my wallet..."
    print =<< pVC <$> readIORef alice
    aliceBcastLost <- atomicModifyIORef alice drainBroadcasts

    putStrLn "Bob receives 'lost'"
    modifyIORef bob $ \p -> foldr receive p aliceBcastLost
    print =<< atomicModifyIORef bob deliver
    print =<< pVC <$> readIORef bob

    putStrLn "Alice sends 'found'"
    modifyIORef alice $ send "Found it!"
    print =<< pVC <$> readIORef alice
    aliceBcastFound <- atomicModifyIORef alice drainBroadcasts

    putStrLn "Carol receives 'found'"
    modifyIORef carol $ \p -> foldr receive p aliceBcastFound
    print =<< atomicModifyIORef carol deliver

    putStrLn "Bob receives 'found'"
    modifyIORef bob $ \p -> foldr receive p aliceBcastFound
    print =<< atomicModifyIORef bob deliver
    print =<< pVC <$> readIORef bob

    putStrLn "Carol receives 'lost'"
    modifyIORef carol $ \p -> foldr receive p aliceBcastLost
    print =<< atomicModifyIORef carol deliver
    print =<< pVC <$> readIORef carol

    putStrLn "Carol delivers 'found'"
    print =<< atomicModifyIORef carol deliver
    print =<< pVC <$> readIORef carol


rightExample :: IO ()
rightExample = do
    alice <- newIORef (pNew 0 3 :: Process String)
    bob   <- newIORef (pNew 1 3 :: Process String)
    carol <- newIORef (pNew 2 3 :: Process String)

    putStrLn "Alice sends 'lost'"
    modifyIORef alice $ send "I lost my wallet..."
    print =<< pVC <$> readIORef alice
    aliceBcastLost <- atomicModifyIORef alice drainBroadcasts

    putStrLn "Bob receives 'lost'"
    modifyIORef bob $ \p -> foldr receive p aliceBcastLost
    print =<< atomicModifyIORef bob deliver
    print =<< pVC <$> readIORef bob

    putStrLn "Alice sends 'found'"
    modifyIORef alice $ send "Found it!"
    print =<< pVC <$> readIORef alice
    aliceBcastFound <- atomicModifyIORef alice drainBroadcasts

    putStrLn "Bob receives 'found'"
    modifyIORef bob $ \p -> foldr receive p aliceBcastFound
    print =<< atomicModifyIORef bob deliver
    print =<< pVC <$> readIORef bob

    putStrLn "Carol receives ' lost'"
    modifyIORef carol $ \p -> foldr receive p aliceBcastLost
    print =<< atomicModifyIORef carol deliver
    print =<< pVC <$> readIORef carol

    putStrLn "Bob sends 'glad'"
    modifyIORef bob $ send "Glad to hear it!"
    print =<< pVC <$> readIORef bob
    bobBcastGlad <- atomicModifyIORef bob drainBroadcasts

    putStrLn "Alice receives 'glad'"
    modifyIORef alice $ \p -> foldr receive p bobBcastGlad
    print =<< atomicModifyIORef alice deliver
    print =<< atomicModifyIORef alice deliver
    print =<< atomicModifyIORef alice deliver
    print =<< pVC <$> readIORef alice

    putStrLn "Carol receives 'glad'"
    modifyIORef carol $ \p -> foldr receive p bobBcastGlad
    print =<< atomicModifyIORef carol deliver

    putStrLn "Carol receives 'found'"
    modifyIORef carol $ \p -> foldr receive p aliceBcastFound
    print =<< atomicModifyIORef carol deliver
    print =<< pVC <$> readIORef carol

    putStrLn "Carol delivers 'glad'"
    print =<< atomicModifyIORef carol deliver
    print =<< pVC <$> readIORef carol
