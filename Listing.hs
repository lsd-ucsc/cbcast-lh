{-# OPTIONS_GHC "-Wno-missing-signatures" #-}
{-# OPTIONS_GHC "-Wno-orphans" #-}
{-# LANGUAGE StandaloneDeriving #-}

import Data.Tuple
import Data.IORef

import MessagePassingAlgorithm
import MessagePassingAlgorithm.VectorClockAdapter
import MessagePassingAlgorithm.CBCAST

broadcast = internalBroadcast
receive = internalReceive
deliver = internalDeliver

deriving instance (Show mm, Show r) => Show (Message mm r)
deriving instance (Show mm, Show r) => Show (Event mm r)
deriving instance Show VCMM
deriving instance Show r => Show (P r)

modifyIORefMaybe :: IORef a -> (a -> Maybe (a, b)) -> IO (Maybe b)
modifyIORefMaybe ref f =
    atomicModifyIORef ref $
    \a -> case f a of Nothing      -> (a, Nothing)
                      Just (a', b) -> (a', Just b)


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
    alice <- newIORef (pEmpty n 0 :: P String)
    bob   <- newIORef (pEmpty n 1 :: P String)
    carol <- newIORef (pEmpty n 2 :: P String)

    -- Alice sends 'lost' and their VC increments to [1,0,0].
    mLost <- atomicModifyIORef alice $ swap . broadcast "I lost my wallet..."

    -- Alice sends 'found' and their VC increments to [2,0,0].
    mFound <- atomicModifyIORef alice $ swap . broadcast "Found it!"

    -- Carol receives 'found' and delays it because it depends on 'lost'.
    modifyIORef carol $ receive mFound
    Nothing <- modifyIORefMaybe carol $ fmap swap . deliver

    -- Carol receives 'lost' and delivers it, updating their VC to [1,0,0].
    modifyIORef carol $ receive mLost
    Just Message{mRaw="I lost my wallet..."} <- modifyIORefMaybe carol $ fmap swap . deliver

    -- Carol delivers 'found', updating their VC to [2,0,0]
    Just Message{mRaw="Found it!"} <- modifyIORefMaybe carol $ fmap swap . deliver

    print =<< readIORef alice
    print =<< readIORef bob
    print =<< readIORef carol


rightExample :: IO ()
rightExample = do
    -- Three causal broadcast processes which send String messages.
    let n = 3
    alice <- newIORef (pEmpty n 0 :: P String)
    bob   <- newIORef (pEmpty n 1 :: P String)
    carol <- newIORef (pEmpty n 2 :: P String)

    -- Alice sends 'lost' and their VC increments to [1,0,0].
    mLost <- atomicModifyIORef alice $ swap . broadcast "I lost my wallet..."

    -- Alice sends 'found' and their VC increments to [2,0,0].
    mFound <- atomicModifyIORef alice $ swap . broadcast "Found it!"

    -- Bob receives both 'lost' and 'found' and delivers them in causal order,
    -- updating their VC to [2,0,0].
    modifyIORef bob $ receive mFound
    modifyIORef bob $ receive mLost
    Just (Message{mRaw="I lost my wallet..."}) <- modifyIORefMaybe bob $ fmap swap . deliver
    Just (Message{mRaw="Found it!"}) <- modifyIORefMaybe bob $ fmap swap . deliver

    -- Carol receives 'lost' and delivers it, updating their VC to [1,0,0].
    modifyIORef carol $ receive mLost
    Just (Message{mRaw="I lost my wallet..."}) <- modifyIORefMaybe carol $ fmap swap . deliver

    -- Bob sends 'glad' and their VC increments to [2,1,0].
    mGlad <- atomicModifyIORef bob $ swap . broadcast "Glad to hear it!"

    -- Carol receives 'glad' and delays it because it depends on 'found'.
    modifyIORef carol $ receive mGlad
    Nothing <- modifyIORefMaybe carol $ fmap swap . deliver

    -- Carol receives 'found' and delivers it, updating their VC to [2,0,0].
    modifyIORef carol $ receive mFound
    Just (Message{mRaw="Found it!"}) <- modifyIORefMaybe carol $ fmap swap . deliver

    -- Carol delivers 'glad', updating their VC to [2,1,0].
    Just (Message{mRaw="Glad to hear it!"}) <- modifyIORefMaybe carol $ fmap swap . deliver

    print =<< readIORef alice
    print =<< readIORef bob
    print =<< readIORef carol
