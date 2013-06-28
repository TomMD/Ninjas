{-# LANGUAGE DeriveDataTypeable #-}
-- | White belts are able to use basic logical to
-- indicate when to attack and where to move.  Due to lack of training,
-- they don't pay attention to deals, like if their target is already
-- dead.  As a result, the whitebelts is most dangerous to himself.
module Ninja.WhiteBelt
    ( Ninja, Stance, MoveOp(..), Cond(..)
    , whiteBelt, horse
    ) where

import Ninja
import Bot
import qualified NetworkMessages as NM
import qualified Simulation as S
import Parameters

import Control.Monad.Random
import Control.Monad (unless)
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Data.Dynamic
import VectorUtils
import Graphics.Gloss.Data.Vector (magV, dotV, argV, unitVectorAtAngle)
import Graphics.Gloss.Data.Point
import Data.List
import Data.Ord
import Data.Data

data MoveOp
    = Stop         -- ^ Stay still
    | AvoidEnemy   -- ^ Walk away from the closest person
    | TowardEnemy  -- ^ Walk toward the closest person
    | ToCastle     -- ^ Walk toward the closest castle
    | RandomWalk   -- ^ Walk somewhere random
    | Attack       -- ^ Swing your sword!
    | Continue     -- ^ Do nothing different

evalMove :: BotHandle -> Int -> [Point] -> InfoWorld -> MoveOp -> IO ()
evalMove bh _ _ _ Stop = stop bh
evalMove bh self _ w AvoidEnemy  = do
    let nme  = getClosestEnemy self w
    case nme of
        Nothing -> return ()
        Just e -> do
            let me   = getSelf self w
                newDir = unitVectorAtAngle $ (pi/2) + argV (charFacing e)
                dest = addPt (charPos me) (mulPt (10,10) newDir)
                mulPt (x1,x2) (y1,y2) = (x1*y1,x2*y2)
            move bh dest
evalMove bh self _ w TowardEnemy = do
    let e = getClosestEnemy self w
    maybe (return ()) (move bh . charPos) e
evalMove bh self cs w ToCastle = do
    let me = getSelf self w
        t  = minimumBy (comparing (distance (charPos me))) cs
    unless (null cs) (move bh t)
evalMove bh _ _ _ RandomWalk  = do
    x <- randomRIO (fst boardMin, fst boardMax)
    y <- randomRIO (snd boardMin, snd boardMax)
    let dst = (x,y)
    move bh dst
evalMove bh _ _ _ Attack = attack bh
evalMove _  _ _ _ Continue = return ()

data Cond = EnemyInReach        -- ^ Closest enemy within striking range
          | EnemyFacing       -- ^ Closest enemy is facing toward you
          | EnemyBackTurned     -- ^ Closest enemy is facing away from you
          | EnemyBehind         -- ^ Closest enemy is behind you
          | EnemyInFront        -- ^ Closest enemy is infront of you
          -- | JustStruck          -- ^ You have _just_ struck at an enemy
          | Stopped             -- ^ You are stopped
          | CondRandom Float    -- ^ Randomly with a probability (0-1)
          | AND Cond Cond
          | OR Cond Cond

consideringClosest :: (Character -> Character -> Bool) -> Int -> InfoWorld -> Bool
consideringClosest f self w =
    let enemy = getClosestEnemy self w
        me    = getSelf self w
    in maybe False (`f` me) enemy

evalCond :: RandomGen g => Int -> InfoWorld -> Cond -> Rand g Bool
evalCond self w (AND a b) = do
    let e = evalCond self w
    aE <- e a
    bE <- e b
    return (aE && bE)
evalCond self w (OR a b) = do
    let e = evalCond self w
    aE <- e a
    bE <- e b
    return (aE || bE)
evalCond self w EnemyInReach =
    return $ consideringClosest (\n me -> n `S.canHitPoint` charPos me) self w

evalCond self w EnemyFacing = return $ consideringClosest facing self w
evalCond self w EnemyBackTurned = not `fmap` evalCond self w EnemyFacing
evalCond self w EnemyBehind  = not `fmap` evalCond self w EnemyInFront
evalCond self w EnemyInFront = return $ consideringClosest (flip facing) self w
-- evalCond self w JustStruck = not implemented
evalCond self w Stopped = do
    let me = getSelf self w
    return $ case charState me of
                Waiting _ -> True
                _ -> False
evalCond _ _ (CondRandom p) = do
    r <- getRandomR (0,1)
    return $ r <= p

-- @a `facing` b@ is True iff @b@ is in the attack angle of @a@.
facing :: Character -> Character -> Bool
facing a b = cos attackAngle <= charFacing a `dotV`
             subPt (charPos b) (charPos a)

getSelf :: Int -> InfoWorld -> Character
getSelf k w = maybe (error "Self not found") id
                            (IntMap.lookup k (everyone w))

getClosestEnemy :: Int -> InfoWorld -> Maybe Character
getClosestEnemy me w =
    let self        = getSelf me w
        dist targ = distance (charPos targ) (charPos self)
    in minimumMayBy (comparing dist)
       . IntMap.elems . everyoneElse me $ w

distance :: Point -> Point -> Float
distance p1 p2 = magV $ subPt p1 p2

minimumMayBy :: (a -> a -> Ordering) -> [a] -> Maybe a
minimumMayBy _ [] = Nothing
minimumMayBy f xs = Just (minimumBy f xs)

everyone :: InfoWorld -> IntMap Character
everyone = infoCharacters

everyoneElse :: Int -> InfoWorld -> IntMap Character
everyoneElse me = IntMap.filterWithKey (\k _ -> k /= me) . everyone

whiteBelt :: [(Cond,MoveOp)] -> Ninja
whiteBelt _ _ (Cmd (NM.SetWorld _,_))  _ = return $ toDyn Init
whiteBelt _ _ (Cmd (NM.ServerReady,_)) _ = return $ toDyn Init
whiteBelt conds bh be stance = do
    newStance <- identifySelf bh be stance
    case newStance of
        KnowSelf self cs -> do
            let selfLoc = charPos (getSelf self w)
                cs' = filter (not . (selfLoc `S.isInPillar`)) cs
            case be of
                Tick _ -> kata self cs'
                _      -> return ()
            return $ toDyn $ KnowSelf self cs'
        _                -> return (toDyn newStance)
  where
  w = worldOf be

  kata :: Int -> [Point] -> IO ()
  kata self cs = go self cs conds

  go :: Int -> [Point] -> [(Cond,MoveOp)] -> IO ()
  go _ _    []     = return ()
  go self remPillars ((c,m):cs) = do
    g <- newStdGen
    if evalRand (evalCond self w c) g
        then evalMove bh self remPillars w m
        else go self remPillars cs

-- |By issuing a random initial move we can identify ourselves with very
-- high probability.

identifySelf :: BotHandle -> BotEvent -> Dynamic -> IO Horse
identifySelf bh be dyn =
    case fromDyn dyn Init of
        Init -> doMove
        x@(MoveTo dst ticks) ->
            case be of
                Cmd (NM.ServerCommand i (NM.Move _ p),_) | p == dst ->
                    return $ KnowSelf i pillars
                Tick _ -> if ticks > maxTicksForSelfId
                           then doMove
                           else return (MoveTo dst (ticks + 1))
                _ -> return x
        x -> return x
  where
  maxTicksForSelfId = 20 -- 1 second assuming the default 20hz
  doMove = do
    x <- randomRIO (fst boardMin, fst boardMax)
    y <- randomRIO (snd boardMin, snd boardMax)
    let dst = (x,y)
    move bh dst
    return $ MoveTo dst 0

-- | With the horse stance a ninja truely knows one's self.
horse :: Stance
horse = toDyn (Init :: Horse)

data Horse = MoveTo Point Int | KnowSelf Int [Point] | Init
    deriving (Data,Typeable)
