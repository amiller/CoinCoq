-- Author: Andrew Miller <amiller@dappervision.com>

-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this file,
-- You can obtain one at http://mozilla.org/MPL/2.0/.

-- This is an adaptation of roconnor's Purecoin (haskell bitcoin impl)
-- Script.hs.
-- 
-- The idea here is to express the bitcoin validation 'machine'
-- as a monadic action on a *class* of monads, rather than for a single
-- specific monad.
-- 


import Control.Monad
import Control.Monad.State (StateT, get, put, execStateT, runStateT, evalStateT)
import Control.Monad.Error (Error, ErrorT, runErrorT)
import Control.Monad.State.Class (MonadState)
import Control.Monad.Error.Class (MonadError)
import Control.Monad.Identity (Identity)


class Monad m => BtcMachineT m where
  push :: String -> m ()
  pop  :: m String
  swap :: m ()
  depth :: m Int


instance Monad m => BtcMachine (StateT ([String],[String]) (ErrorT String m)) where
  push s = do (main,alt) <- get; put (s:main,alt) >> return ()
  pop    = do (s:main,alt) <- get; put (main,alt) >> return s
  swap   = do (main,alt) <- get; put (alt,main) >> return ()
  depth  = do (main,_) <- get; return $ length main


data OpCode = 
    OP_DUP | OP_DROP | OP_IFDUP | OP_1 | OP_DEPTH 
  | OP_TOALTSTACK | OP_FROMALTSTACK | OP_RETURN
  deriving (Eq, Show)


execOp :: BtcMachine m => OpCode -> m ()
execOp OP_1 = push "1"
execOp OP_DUP = do x1 <- pop; push x1 >> push x1
execOp OP_DROP = pop >> return ()
execOp OP_IFDUP = do x1 <- pop; push x1 >> when (x1 /= "") (push x1)
execOp OP_DEPTH = do n <- depth; push (show n)
execOp OP_TOALTSTACK = do x1 <- pop; swap >> push x1 >> swap
execOp OP_FROMALTSTACK = do swap >> do x1 <- pop; swap >> push x1
execOp OP_RETURN = fail "OP_RETURN"


runBtcMachine :: Monad m => [OpCode] -> m (Either String ((), ([String], [String])))
runBtcMachine ops = runErrorT $ runStateT (mapM_ execOp ops) ([], [])

test1 :: Monad m => Int -> m (Either String ((), ([String], [String])))
test1 0 = runBtcMachine [OP_1, OP_DUP, OP_DUP, OP_DEPTH, OP_DEPTH, OP_DEPTH, OP_DEPTH, OP_TOALTSTACK]
test1 1 = runBtcMachine [OP_1, OP_DUP, OP_RETURN]
test1 2 = runBtcMachine [OP_1, OP_DUP, OP_IFDUP]

-- go :: OpCode -> BtcMachineId
-- go i = execOp i

-- evalInit :: OpCode -> Error String ([String],[String])
-- evalInit i = execStateT BtcMachineId ([], [])
