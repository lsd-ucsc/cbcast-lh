
import Control.Concurrent.STM

import CBCAST

-- | Example figures in the paper (the corrected Alice/Bob/Carol executions).
main :: IO ()
main = do
    leftExample
    putStrLn $ replicate 10 '='
    rightExample


leftExample :: IO ()
leftExample = do
    -- Three causal broadcast processes which send String messages.
    let n = 3
    alice <- newTVarIO (either error id $ newProcess n 0 :: Process String)
    bob   <- newTVarIO (either error id $ newProcess n 1 :: Process String)
    carol <- newTVarIO (either error id $ newProcess n 2 :: Process String)

    -- Alice sends 'lost' and their VC increments.
    mLost <- atomically . stateTVar alice $ broadcast "I lost my wallet..."
    [1,0,0] <- atomically $ pVC <$> readTVar alice

    -- Alice sends 'found' and their VC increments.
    mFound <- atomically . stateTVar alice $ broadcast "Found it!"
    [2,0,0] <- atomically $ pVC <$> readTVar alice

    -- Carol receives 'found' and delays it because it depends on 'lost'.
    atomically . modifyTVar carol $ either error id . receive mFound
    Nothing <- atomically $ stateTVar carol deliver

    -- Carol receives 'lost' and delivers it, updating their VC.
    atomically . modifyTVar carol $ either error id . receive mLost
    Just "I lost my wallet..." <- atomically $ fmap mRaw <$> stateTVar carol deliver
    [1,0,0] <- atomically $ pVC <$> readTVar carol

    -- Carol delivers 'found', updating their VC.
    Just "Found it!" <- atomically $ fmap mRaw <$> stateTVar carol deliver
    [2,0,0] <- atomically $ pVC <$> readTVar carol

    print =<< readTVarIO alice
    print =<< readTVarIO bob
    print =<< readTVarIO carol


rightExample :: IO ()
rightExample = do
    -- Three causal broadcast processes which send String messages.
    let n = 3
    alice <- newTVarIO (either error id $ newProcess n 0 :: Process String)
    bob   <- newTVarIO (either error id $ newProcess n 1 :: Process String)
    carol <- newTVarIO (either error id $ newProcess n 2 :: Process String)

    -- Alice sends 'lost' and their VC increments.
    mLost <- atomically . stateTVar alice $ broadcast "I lost my wallet..."
    [1,0,0] <- atomically $ pVC <$> readTVar alice

    -- Alice sends 'found' and their VC increments.
    mFound <- atomically . stateTVar alice $ broadcast "Found it!"
    [2,0,0] <- atomically $ pVC <$> readTVar alice

    -- Bob receives both 'lost' and 'found' and delivers them in causal order,
    -- updating their VC.
    atomically . modifyTVar bob $ either error id . receive mFound
    atomically . modifyTVar bob $ either error id . receive mLost
    Just "I lost my wallet..." <- atomically $ fmap mRaw <$> stateTVar bob deliver
    [1,0,0] <- atomically $ pVC <$> readTVar bob
    Just "Found it!" <- atomically $ fmap mRaw <$> stateTVar bob deliver
    [2,0,0] <- atomically $ pVC <$> readTVar bob

    -- Carol receives 'lost' and delivers it, updating their VC.
    atomically . modifyTVar carol $ either error id . receive mLost
    Just "I lost my wallet..." <- atomically $ fmap mRaw <$> stateTVar carol deliver
    [1,0,0] <- atomically $ pVC <$> readTVar carol

    -- Bob sends 'glad' and their VC increments to.
    mGlad <- atomically . stateTVar bob $ broadcast "Glad to hear it!"
    [2,1,0] <- atomically $ pVC <$> readTVar bob

    -- Carol receives 'glad' and delays it because it depends on 'found'.
    atomically . modifyTVar carol $ either error id . receive mGlad
    Nothing <- atomically $ stateTVar carol deliver

    -- Carol receives 'found' and delivers it, updating their VC.
    atomically . modifyTVar carol $ either error id . receive mFound
    Just "Found it!" <- atomically $ fmap mRaw <$> stateTVar carol deliver
    [2,0,0] <- atomically $ pVC <$> readTVar carol

    -- Carol delivers 'glad', updating their VC.
    Just "Glad to hear it!" <- atomically $ fmap mRaw <$> stateTVar carol deliver
    [2,1,0] <- atomically $ pVC <$> readTVar carol

    print =<< readTVarIO alice
    print =<< readTVarIO bob
    print =<< readTVarIO carol
