module Interpreter where

import Prog
import qualified Disk
import Word
import qualified Crypto.Hash.SHA256 as SHA256
-- import qualified System.Exit
-- import qualified System.Random

-- crashRandom :: IO Int
-- crashRandom = System.Random.getStdRandom (System.Random.randomR (1, 20))

-- maybeCrash :: IO ()
-- maybeCrash = do
--   x <- crashRandom
--   -- if x == 1
--   if x == 0
--   then
--     do
--       putStrLn "CRASH!"
--       System.Exit.exitFailure
--   else
--     return ()

verbose :: Bool
verbose = False

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then
    putStrLn s
  else
    return ()

run_dcode :: Disk.DiskState -> Prog.Coq_prog a -> IO a
run_dcode _ (Ret r) = do
  debugmsg $ "Done"
  return r
run_dcode ds (Read a) = do
  debugmsg $ "Read " ++ (show a)
  val <- Disk.read_disk ds a
  return $ unsafeCoerce val
run_dcode ds (Write a v) = do
  debugmsg $ "Write " ++ (show a) ++ " " ++ (show v)
  Disk.write_disk ds a v
  return $ unsafeCoerce ()
run_dcode ds Sync = do
  debugmsg $ "Sync"
  Disk.sync_disk ds
  return $ unsafeCoerce ()
run_dcode ds (Trim a) = do
  debugmsg $ "Trim " ++ (show a)
  Disk.trim_disk ds a
  return $ unsafeCoerce ()
run_dcode ds (Hash sz (W64 w)) = run_dcode ds (Hash sz (W $ fromIntegral w))
run_dcode _ (Hash sz (W w)) = do
  debugmsg $ "Hash " ++ (show sz) ++ " " ++ (show w)
  wbs <- Disk.i2bs w $ fromIntegral $ (sz + 7) `div` 8
  h <- return $ SHA256.hash wbs
  ih <- Disk.bs2i h
  return $ unsafeCoerce $ W ih
run_dcode ds (Bind p1 p2) = do
  debugmsg $ "Bind"
  r1 <- run_dcode ds p1
  r2 <- run_dcode ds (p2 r1)
  return r2

run :: Disk.DiskState -> Prog.Coq_prog a -> IO a
run ds p = run_dcode ds p
