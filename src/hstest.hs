module Main where

import System.Posix.IO
import MemLog
import Balloc
import Inode
import Word
import qualified Interpreter as I
import qualified System.Directory
import qualified Testprog

disk_fn :: String
disk_fn = "disk.img"

-- the_prog :: Log.Coq_xparams -> Prog.Coq_prog ()
-- the_prog xp =
--   _LOG__init xp $ \_ ->
--   _LOG__begin xp $ \_ ->
--   _LOG__read xp (W64 5) $ \v ->
--   _LOG__write xp (W64 6) v $ \_ ->
--   _LOG__commit xp $ \_ ->
--   Prog.Done ()

lxp :: MemLog.Coq_xparams
lxp = MemLog.Build_xparams
  (W 0x2000)  -- log header sector
  (W 0x2001)  -- commit flag sector
  (W 0x2010)  -- log start sector
  (W 0x40)    -- log length (at most addr_per_block), and MemLog uses one more for a block of addrs

bxp :: Balloc.Coq_xparams
bxp = Balloc.Build_xparams
  (W 0x1100)  -- bitmap start sector
  (W 0x1)     -- bitmap length

ixp :: Inode.Coq_xparams
ixp = Inode.Build_xparams
  (W 0x1000)   -- inode start sector
  (W 0x100)    -- number of inode sectors

repf :: Integer -> t -> (t -> IO t) -> IO t
repf 0 x _ = return x
repf n x f = do
  y <- f x
  z <- repf (n-1) y f
  return z

main :: IO ()
main = do
  -- This is racy (stat'ing the file first and opening it later)
  fileExists <- System.Directory.doesFileExist disk_fn
  fd <- openFd disk_fn ReadWrite (Just 0o666) defaultFileFlags
  if fileExists
  then
    do
      putStrLn "Recovering disk.."
      I.run fd $ _MEMLOG__recover lxp
  else
    do
      putStrLn "Initializing disk.."
      I.run fd $ _MEMLOG__init lxp
  putStrLn "Running program.."
  -- r <- I.run fd $ the_prog lxp
  -- r <- I.run fd $ Testprog.testcopy lxp
  -- r <- I.run fd $ Testprog.testalloc lxp bxp
  r <- repf 10000 (Just (W 123))
       (\x -> case x of
              Nothing -> return Nothing
              Just xv -> I.run fd $ Testprog.test_bfile lxp bxp ixp xv)
  closeFd fd
  putStrLn $ "Done: " ++ (show r)

