{-
* Karma.hs
* Author: Jaafar Mohammed
* Version: 1.0
* Date: Dec 2025
-}
module KarmaBrief where

import System.Random
import Control.Monad.State
import Control.Monad (replicateM, forM, mapM, mplus)
import Data.List
import Data.Ord
import Data.Maybe ( listToMaybe, fromJust, fromMaybe, isJust, catMaybes)

-- Cards
data Suit = Clubs | Diamonds | Hearts | Spades
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

data Rank = R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | RJ | RQ | RK | RA
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

data Card = Card { rank :: Rank, suit :: Suit }
  deriving (Eq, Show, Read)

type Deck = [Card]
type Pile = [Card]

-- Players
type PlayerId   = Int
type PlayerName = String

data Player = Player
  { pId       :: PlayerId
  , pName     :: PlayerName
  , hand      :: [Card]
  , faceUp    :: [Card]
  , faceDown  :: [Card]
  , strategy  :: String
  } deriving (Eq, Show)

-- Game state 
data GameState = GameState
  { players       :: [Player]    -- clockwise order
  , currentIx     :: Int         -- index into players
  , drawPile      :: Deck
  , discardPile   :: Pile
  , burnedPiles   :: [Pile]
  , rng           :: StdGen      -- random number generator
  , playDirection :: Int         -- 1 = clockwise, -1 = counter-clockwise
  , activeExtensions :: [Extension]
  , finishedOrder :: [PlayerId]
  , winners       :: [PlayerName]
  , turnCount     :: Int
  } deriving (Show);

-- Different extension rules we can toggle
data Extension = ExtReverse8 | ExtThree3s | ExtNineClubs
  deriving (Eq, Show)

-- Creating a deck 
startDeck :: Deck
startDeck =
  let
    allRanks = [R2, R3, R4, R5, R6, R7, R8, R9, R10, RJ, RQ, RK, RA]
  in
  [Card r s | r <- allRanks, s <- [Clubs, Diamonds, Hearts, Spades]]

isSpecialCard :: Card -> Bool
isSpecialCard c = isResetCard c || isBurnCard c || isStealCard c || isReverseCard c

isReverseCard :: Card -> Bool
isReverseCard (Card R8 _) = True
isReverseCard _ = False

isResetCard :: Card -> Bool
isResetCard (Card R2 _) = True
isResetCard _ = False

isBurnCard :: Card -> Bool
isBurnCard (Card R10 _) = True
isBurnCard _ = False

isStealCard :: Card -> Bool
isStealCard (Card R9 Clubs) = True
isStealCard _ = False

--------------------------------------------------------------------------------
-- Step 1 
--------------------------------------------------------------------------------
legalPlay :: Maybe Card -> Card -> Bool
legalPlay Nothing _ = True
legalPlay (Just topCard) playersCard
    | rank playersCard >= rank topCard = True
    | rank topCard == R7 && rank playersCard <= R7 = True
    | rank playersCard == R2 || rank playersCard == R8 || rank playersCard == R10 = True
    | rank topCard == R2 = True
    | otherwise = False

validPlays :: Maybe Card -> Deck -> Deck
validPlays _ [] = []
validPlays Nothing hand = hand
validPlays (Just topCard) (x:xs)
    -- Recursively calls validPlays if the top card is a legalPlay
    | legalPlay (Just topCard) x = x : validPlays (Just topCard) xs
    | otherwise = validPlays (Just topCard) xs

dealCards :: Int -> State GameState Deck
dealCards n = do
  -- Get the current game state
  currentState <- get
  let currentDrawPile = drawPile currentState
      (cardsToDeal, newDrawPile) = splitAt n currentDrawPile
      newState = currentState{ drawPile = newDrawPile }

  put newState
  return cardsToDeal

giveWastePileTo :: Player -> State GameState ()
giveWastePileTo player = do
  currentState <- get
  let currentPlayerHand = hand player
      currentPile = discardPile currentState
      newHand = currentPlayerHand ++ currentPile
      updatedPlayer = player{ hand = newHand }

      -- Rebuild players list with updated player
      updatedPlayersList =
        [ if pId p == pId updatedPlayer
          then updatedPlayer
          else p
        | p <- players currentState ]

      -- Putting new state with updated players and empty discard pile
      newState = currentState { players = updatedPlayersList, discardPile = [] }

  put newState
  return ()

replenishCards :: Player -> State GameState ()
replenishCards player = do
  currentState <- get
  let currentPlayerHand = hand player
      currentDrawPile = drawPile currentState
      cardsNeeded = 3 - length currentPlayerHand

  if currentDrawPile /= [] && cardsNeeded > 0
  then do
    let cardsDrawn = take cardsNeeded currentDrawPile
        newDrawPile = drop cardsNeeded currentDrawPile
        newHand = currentPlayerHand ++ cardsDrawn
        updatedPlayer = player{ hand = newHand }

        updatedPlayersList =
          [ if pId p == pId updatedPlayer
            then updatedPlayer
            else p
          | p <- players currentState ]

        newState = currentState { players = updatedPlayersList, drawPile = newDrawPile }

    put newState
  else
    return ()

shuffleDeck :: StdGen -> Deck -> Deck
shuffleDeck g xs =
  let
    cmp :: (a, Int) -> (a, Int) -> Ordering
    cmp (_, y1) (_, y2) = compare y1 y2

    rs :: [Int]
    rs = randoms g

  in [card | (card, _) <- sortBy cmp (zip xs rs)]

--------------------------------------------------------------------------------
-- Step 2 
--------------------------------------------------------------------------------
basicStrategy :: State GameState Deck
basicStrategy = do
  currentState <- get
  let playersList = players currentState
      playerIx = currentIx currentState
      currentPlayer = playersList !! playerIx
      currentPlayerHand = hand currentPlayer
      currentDrawPile = drawPile currentState
      faceUpCards = faceUp currentPlayer
      faceDownCards = faceDown currentPlayer
      currentGamePile = discardPile currentState
      topCard :: Maybe Card
      topCard = listToMaybe currentGamePile -- Retrieves Maybe Card from discard pile

  if currentPlayerHand /= []
  then do
    let validCards = validPlays topCard currentPlayerHand
        chooseCard :: Deck -> Deck
        chooseCard [] = []
        chooseCard cards = [minimumBy (comparing rank) cards]
        cardChosenDeck = chooseCard validCards 
    return cardChosenDeck
  else if currentPlayerHand == [] && currentDrawPile == [] && faceUpCards /= []
  then do
    let validCards = validPlays topCard faceUpCards
        chooseCard :: Deck -> Deck
        chooseCard [] = []
        chooseCard cards = [minimumBy (comparing rank) cards]
        cardChosenDeck = chooseCard validCards
    return cardChosenDeck
  else
    do
      let currentGen = rng currentState
          (cardChosenDeck, newGen) = randomCard currentGen faceDownCards
          newState = currentState { rng = newGen } -- Update RNG in state
      put newState
      return [cardChosenDeck]

-- Helper function to get a random card from a list
randomCard :: StdGen -> [Card] -> (Card, StdGen)
randomCard _ [] = error "The list provided is empty"
randomCard g xs =
  let max = length xs - 1
      (randomIndex, g') = randomR (0, max) g
  in (xs !! randomIndex, g')

applyStrategy :: State GameState ()
applyStrategy = do
  currentState <- get
  let playerIx = currentIx currentState
      currentPlayer = players currentState !! playerIx
      currentGamePile = discardPile currentState
      currentDrawPile = drawPile currentState
      currentPlayerHand = hand currentPlayer
      faceUpCards = faceUp currentPlayer
      faceDownCards = faceDown currentPlayer
      topCard = listToMaybe currentGamePile

  -- Check to see which strategy to use
  cardChosenDeck <- if strategy currentPlayer == "Basic"
    then basicStrategy
    else case strategy currentPlayer of
           "BasicSets" -> basicStrategySets
           "Smart"     -> smartStrategy
           _             -> basicStrategySets

  case cardChosenDeck of
    (chosenCard:_) -> do
      let (updatedPlayer, newDiscardPile, finalDrawPile)
            | currentPlayerHand /= [] && not (null cardChosenDeck) =
              let newHand = delete chosenCard currentPlayerHand
                  (finalHand, updatedDrawPile) = replenishHand newHand currentDrawPile
              in (currentPlayer { hand = finalHand }, [chosenCard] ++ currentGamePile, updatedDrawPile)

            | null currentPlayerHand && null currentDrawPile && faceUpCards /= [] && not (null cardChosenDeck) =
              let newFaceUp = delete chosenCard faceUpCards
              in (currentPlayer { faceUp = newFaceUp }, [chosenCard] ++ currentGamePile, currentDrawPile)

            | null currentPlayerHand && null currentDrawPile && null faceUpCards && not (null cardChosenDeck) =

              if legalPlay topCard chosenCard
              then
                let newFaceDown = delete chosenCard faceDownCards
                in (currentPlayer { faceDown = newFaceDown }, [chosenCard] ++ currentGamePile, currentDrawPile)
              else
                let newHand = currentPlayerHand ++ faceDownCards ++ faceUpCards ++ [chosenCard] ++ currentGamePile
                in (currentPlayer { hand = newHand, faceDown = [], faceUp = [] }, [], currentDrawPile)

            | otherwise =
              error "Chosen card is defined, but failed to match any guard in applyStrategy."

      -- Apply burn rule if R10 played
      let finalDiscardPile =
            if rank chosenCard == R10
              then []
            else newDiscardPile

      let baseUpdatedPlayersList =
            [ if pId p == pId updatedPlayer
               then updatedPlayer
               else p
            | p <- players currentState ]


      -- Handling extensions
      let exts = activeExtensions currentState
      if rank chosenCard == R8 && (ExtReverse8 `elem` exts)
        then do
          let newBurned = if rank chosenCard == R10 then burnedPiles currentState ++ [newDiscardPile] else burnedPiles currentState
              newState = currentState { players = baseUpdatedPlayersList
                                      , discardPile = finalDiscardPile
                                      , drawPile = finalDrawPile
                                      , playDirection = negate (playDirection currentState)
                                      , burnedPiles = newBurned
                                      }
          put newState
          return ()
        else if isStealCard chosenCard && (ExtNineClubs `elem` exts)
          then do
            let playersList = players currentState
                numPlayers = length playersList
                dir = playDirection currentState
                nextIx = (playerIx + dir + numPlayers) `mod` numPlayers
                opponent = playersList !! nextIx
                oppHand = hand opponent

            if not (null oppHand)
              then do
                let currentGen = rng currentState
                    (randIdx, newGen) = randomR (0, length oppHand - 1) currentGen
                    stolenCard = oppHand !! randIdx
                    newOppHand = delete stolenCard oppHand
                    newUpdatedPlayer = updatedPlayer { hand = hand updatedPlayer ++ [stolenCard] }

                    updatedPlayersAfterSteal = [ if pId p == pId newUpdatedPlayer then newUpdatedPlayer
                                               else if pId p == pId opponent then opponent { hand = newOppHand }
                                               else p
                                             | p <- playersList ]

                    newBurned = if rank chosenCard == R10 then burnedPiles currentState ++ [newDiscardPile] else burnedPiles currentState
                    newState = currentState { players = updatedPlayersAfterSteal
                                            , discardPile = finalDiscardPile
                                            , drawPile = finalDrawPile
                                            , rng = newGen
                                            , burnedPiles = newBurned }

                put newState
                return ()
              else do
                -- Nothing to steal, apply normal update
                let newBurned = if rank chosenCard == R10 then burnedPiles currentState ++ [newDiscardPile] else burnedPiles currentState
                    newState = currentState { players = baseUpdatedPlayersList
                                            , discardPile = finalDiscardPile
                                            , drawPile = finalDrawPile
                                            , burnedPiles = newBurned }
                put newState
                return ()
          else do
            -- Normal play
            let newBurned = if rank chosenCard == R10 then burnedPiles currentState ++ [newDiscardPile] else burnedPiles currentState
                newState = currentState { players = baseUpdatedPlayersList
                                        , discardPile = finalDiscardPile
                                        , drawPile = finalDrawPile
                                        , burnedPiles = newBurned }
            put newState
            return ()
    
    -- No valid card to play (pick up discard pile)
    [] -> do
      let newHand = currentPlayerHand ++ currentGamePile
          updatedPlayer = currentPlayer { hand = newHand }

          updatedPlayersList =
            [ if pId p == pId updatedPlayer
               then updatedPlayer
               else p
            | p <- players currentState ]

          newState = currentState { players = updatedPlayersList,
          discardPile = [] }

      put newState
      return ()

-- Helper for apply strategy
replenishHand :: Deck -> Deck -> (Deck, Deck)
replenishHand currentHand drawPile =
    let cardsNeededNum = 3 - length currentHand
    in if cardsNeededNum > 0 && not (null drawPile)
       then
           let (cardsToAdd, remainingDrawPile) = splitAt cardsNeededNum drawPile
           in (currentHand ++ cardsToAdd, remainingDrawPile)
       else
           (currentHand, drawPile)

gameLoop :: State GameState String
gameLoop = do
  currentState <- get
  -- Early exit on turn limit
  if turnCount currentState >= turnLimit
    then do
      let endMsg = "\n*** GAME ENDED DUE TO TURN LIMIT: " ++ show turnLimit ++ " turns reached. ***\n"
      return endMsg
    else do
      let playersList = players currentState
          playerIx = currentIx currentState
          currentPlayer = playersList !! playerIx
          currentPlayerHand = hand currentPlayer

      if length playersList <= 1
        then do
          outcome <- getGameStatus
          return outcome
        else do
              applyStrategy
              modify (\s -> s { turnCount = turnCount s + 1 })
              currentPlayerOut <- playerOut

              case currentPlayerOut of
                Just _ -> gameLoop
                Nothing -> do
                  nextPlayer
                  gameLoop


-- Helper method for gameLoop (Checks if a player is out)
playerOut :: State GameState (Maybe Player)
playerOut = do
  currentState <- get
  let playersList = players currentState
      playerIx = currentIx currentState
      currentPlayer = playersList !! playerIx
      currentPlayerHand = hand currentPlayer
      currentDrawPile = drawPile currentState
      faceUpCards = faceUp currentPlayer
      faceDownCards = faceDown currentPlayer

  if currentPlayerHand == [] && faceUpCards == [] && faceDownCards == []
    then do
      let newPlayersList = filter (\p -> pName p /= pName currentPlayer) playersList
          newWinnersList = (pName currentPlayer) : (winners currentState)
          newNumPlayers = length newPlayersList
          newIx = if newNumPlayers == 0
            then 0
            else if playerIx >= newNumPlayers
                   then 0
                   else playerIx

          newState = currentState { players = newPlayersList,
          currentIx = newIx, winners = newWinnersList }

      put newState
      return (Just currentPlayer) -- The player that has just gone out
  else
     return Nothing

getGameStatus :: State GameState String
getGameStatus = do
  currentState <- get
  let finalWinnersList = reverse (winners currentState)
      winnerName = head finalWinnersList
      finalMessage = "Game Over! The winner is: " ++ winnerName ++ "."

  return finalMessage

nextPlayer :: State GameState ()
nextPlayer = do
  currentState <- get
  let playersList = players currentState
      numPlayers = length playersList
      dir = playDirection currentState
      nextIx = (currentIx currentState + dir + numPlayers) `mod` numPlayers
  put (currentState { currentIx = nextIx })

-- Implementation of playOneGame
playOneGame :: IO ()
playOneGame =  do
  initialGen <- newStdGen
  let playerNames = ["Player1", "Player2", "Player3"]

      initialDummyState = GameState
        { players = [], currentIx = 0, drawPile = [], discardPile = [], burnedPiles = [],
          rng = initialGen, playDirection = 1, activeExtensions = [], finishedOrder = [], winners = [], turnCount = 0 }

      setupAction = newGame playerNames initialGen

      stateAfterDealing = execState setupAction initialDummyState

      (finalStatus, finalState) = runState gameLoopWithHistory stateAfterDealing

  putStrLn finalStatus
  return ()

dealThreeToEach :: Player -> State GameState Player
dealThreeToEach player = do
  handCards <- dealCards 3
  faceUpCards <- dealCards 3
  faceDownCards <- dealCards 3
  return player { hand = handCards, faceUp = faceUpCards, faceDown = faceDownCards }

-- Putting the players that have been dealt into the game state
putDealtPlayers :: State GameState ()
putDealtPlayers = do
  currentState <- get
  let initialPlayersList = players currentState

  updatedPlayersList <- mapM dealThreeToEach initialPlayersList

  let newState = currentState { players = updatedPlayersList }

  put newState
  return ()

createPlayer :: Int -> String -> Player
createPlayer playerId name = Player
  { pId = playerId
  , pName = name
  , hand = []
  , faceUp = []
  , faceDown = []
  , strategy = "Basic"
  }

newGame :: [String] -> StdGen -> State GameState ()
newGame playerNames g = do
  let shuffledDeck = shuffleDeck g startDeck
      emptyPlayers = zipWith createPlayer [1..3] playerNames

  put GameState
    { players       = emptyPlayers
    , currentIx     = 0
    , drawPile      = shuffledDeck
    , discardPile   = []
    , burnedPiles   = []
    , rng           = g
    , playDirection = 1
    , activeExtensions = []
    , finishedOrder = []
    , winners       = []
    , turnCount     = 0
    }

  putDealtPlayers

-- Implementation of chooseStartingPlayer
chooseStartingPlayer :: State GameState ()
chooseStartingPlayer = findStarterByRank R3

playerWithCard :: [Card] -> Rank -> Bool
playerWithCard [] _ = False
playerWithCard (x:xs) targetRank
  | rank x == targetRank = True
  | otherwise            = playerWithCard xs targetRank

findStarterByRank :: Rank -> State GameState ()
findStarterByRank targetRank = do
  currentState <- get
  let playersList = players currentState
      qualifyingPlayers =
          [player | player <- playersList, playerWithCard (hand player) targetRank]

  case qualifyingPlayers of
    [] -> do
      let nextRank = succ targetRank
      if nextRank > R2
        then do findStarterByRank nextRank
      else return ()

    starters -> do
      let (randomStarterPlayer, nextGen) =
            if length starters == 1
              then
                (head starters, rng currentState)
            else
              let numQualifiers = length starters
                  (randomIndex, newGen) = randomR (0, numQualifiers - 1) (rng currentState)
              in
              (starters !! randomIndex, newGen)

      let maybePlayerIx = findIndex (\p -> pId p == pId randomStarterPlayer) playersList
          newIx = fromJust maybePlayerIx
          newState = currentState { currentIx = newIx, rng = nextGen }

      put newState

--------------------------------------------------------------------------------
-- Step 3 
--------------------------------------------------------------------------------
basicStrategySets:: State GameState Deck
basicStrategySets = do
  currentState <- get
  let playersList = players currentState
      playerIx = currentIx currentState
      currentPlayer = playersList !! playerIx
      currentPlayerHand = hand currentPlayer
      currentDrawPile = drawPile currentState
      faceUpCards = faceUp currentPlayer
      faceDownCards = faceDown currentPlayer
      currentGamePile = discardPile currentState
      topCard :: Maybe Card
      topCard = listToMaybe currentGamePile -- Retrieves Maybe Card from discard pile

  if currentPlayerHand /= []
  then do
    let validCards = validPlays topCard currentPlayerHand
    if null validCards
      then return []
      else do
        let sortedCards = sortBy (comparing rank) validCards
            groupedCards = groupBy (\c1 c2 -> rank c1 == rank c2) sortedCards
            allEqualRankGroups = filter (\g -> length g > 1) groupedCards
            groupsBiggest = sortBy (flip (comparing length)) allEqualRankGroups -- Biggest groups first
            allCardsWithDuplicates = concat allEqualRankGroups
            singleCards = validCards \\ allCardsWithDuplicates
            cardsChosenDeck :: [Card]
            cardsChosenDeck
              | groupsBiggest /= [] = head groupsBiggest
              | otherwise     = [minCard]
              where
                minCard = if null singleCards then minimumBy (comparing rank) validCards
                          else minimumBy (comparing rank) singleCards
        return cardsChosenDeck
  else if currentPlayerHand == [] && currentDrawPile == [] && faceUpCards /= []
  then do
    let validCards = validPlays topCard faceUpCards
    if null validCards
      then return []
      else do
        let sortedCards = sortBy (comparing rank) validCards
            groupedCards = groupBy (\c1 c2 -> rank c1 == rank c2) sortedCards
            allEqualRankGroups = filter (\g -> length g > 1) groupedCards
            groupsBiggest = sortBy (flip (comparing length)) allEqualRankGroups
            allCardsWithDuplicates = concat allEqualRankGroups
            singleCards = validCards \\ allCardsWithDuplicates
            cardsChosenDeck :: [Card]
            cardsChosenDeck
              | groupsBiggest /= [] = head groupsBiggest
              | otherwise     = [minCard]
              where
                minCard = if null singleCards then minimumBy (comparing rank) validCards
                          else minimumBy (comparing rank) singleCards
        return cardsChosenDeck
  else
    do
      let currentGen = rng currentState
          (cardsChosenDeck, newGen) = randomCard currentGen faceDownCards
          newState = currentState { rng = newGen }
      put newState
      return [cardsChosenDeck]

-- Implementation of gameLoopWithHistory
gameLoopWithHistory :: State GameState String
gameLoopWithHistory = do
  currentState <- get
  let playersList = players currentState
      currentDiscardPile = discardPile currentState
      currentBurnedPiles = burnedPiles currentState
      isStart = null (discardPile currentState) && null (burnedPiles currentState)
      currentTurnCount = turnCount currentState

  if currentTurnCount >= turnLimit
    then do
      let endMsg = "\n*** GAME ENDED DUE TO TURN LIMIT: " ++ show turnLimit ++ " turns reached. ***\n"
      getGameStatusHistory
      return (endMsg)

  else if length playersList <= 1
    then do
        getGameStatusHistory
  else do
    let playerIx = currentIx currentState
        currentPlayer = playersList !! playerIx
        currentPlayerName = pName currentPlayer

    (turnLogs, playerRemoved) <- if isStart
      then do
        let openingMsg = "\n-- NEW GAME STARTING --" ++ "\nThe starting player is " ++ currentPlayerName
        preState <- get
        applyStrategy
        postState <- get
        removed <- playerOut
        moveLog <- logMove

        modify (\s -> s { turnCount = turnCount s + 1 })
        return (openingMsg ++ moveLog, removed)
      else do
        let turnMsg = "\nStart of " ++ currentPlayerName ++ "'s turn "

        playerStateLog <- putCurrentPlayerState
        discardPileLog <- putDiscardPile
        preState <- get
        applyStrategy
        postState <- get
        currentPlayerOut <- playerOut

        moveLog <- logMove
        playerOutLog <- logIfPlayerOut
        burnLog <- logIfBurn

        let outLog = fromMaybe "" playerOutLog
            finalBurnLog = fromMaybe "" burnLog

            fullTurnLogs = turnMsg ++ playerStateLog ++ discardPileLog ++ moveLog
                        ++ outLog ++ finalBurnLog

        modify (\s -> s { turnCount = turnCount s + 1 })
        return (fullTurnLogs, currentPlayerOut)


    restOfGameLog <- case playerRemoved of
      Just _ -> do
        gameLoopWithHistory
      Nothing -> do
        nextPlayer
        gameLoopWithHistory

    return (turnLogs ++ restOfGameLog)

-- Helper method for gameLoopWithHistory
getGameStatusHistory :: State GameState String
getGameStatusHistory = do
  currentState <- get
  let finalWinnersList = reverse (winners currentState)
      standingsString = intercalate ", " finalWinnersList
      winnerName = head finalWinnersList
      finalMessage = "\nGAME OVER! The winner is: " ++ winnerName ++ ".\n"
                   ++ "The Standings are: " ++ standingsString

  return finalMessage

logMove :: State GameState String
logMove = do
  currentState <- get
  let currentDiscardPile = discardPile currentState
  case listToMaybe currentDiscardPile of
    Nothing ->
      return "\nThe player attempted a move, but the discard pile is empty. No card logged."
    Just topCard ->
      let finalMessage = "\nThe current move is: " ++ show topCard
      in return finalMessage

putCurrentPlayerState :: State GameState String
putCurrentPlayerState = do
  currentState <- get
  let playersList = players currentState
      playerIx = currentIx currentState
      currentPlayer = playersList !! playerIx
      currentPlayerHand = show (hand currentPlayer)
      faceUpCards = show (faceUp currentPlayer)
      numFaceDown = length (faceDown currentPlayer)

      finalMessage = "-- Current Player State: " ++ pName currentPlayer ++ " --"
                   ++ "\nHand: " ++ currentPlayerHand
                   ++ "\nFace Up Cards: " ++ faceUpCards
                   ++ "\nNumber of Face Down Cards: " ++ show numFaceDown

  return finalMessage

putDiscardPile :: State GameState String
putDiscardPile = do
  currentState <- get
  let currentDiscardPile = show (discardPile currentState)
      finalMessage = "\nThe current discard pile is: " ++ currentDiscardPile

  return finalMessage

logIfBurn :: State GameState (Maybe String)
logIfBurn = do
  currentState <- get
  let currentDiscardPile = discardPile currentState
      currentBurnedPiles = burnedPiles currentState

  if currentDiscardPile == [] && currentBurnedPiles /= []
    then do
      let finalMessage = "The Discard Pile was burned!"

      return (Just finalMessage)
    else
      return Nothing

logIfPlayerOut :: State GameState (Maybe String)
logIfPlayerOut = do
  currentState <- get
  let playersList = players currentState
      playerIx = currentIx currentState
      currentPlayer = playersList !! playerIx

  if hand currentPlayer == [] && faceUp currentPlayer == [] && faceDown currentPlayer == []
    then do
      let playerName = pName currentPlayer
          finalMessage = "Player " ++ playerName ++ " is now out of the game!"

      return (Just finalMessage)
    else
      return Nothing

turnLimit :: Int
turnLimit = 1000

-- Implementation of runOneGameWithHistory
runOneGameWithHistory :: IO ()
runOneGameWithHistory = do
  initialGen <- newStdGen
  let playerNames = ["Player1", "Player2", "Player3"]

      --Dummy state needed to setup game
      initialDummyState = GameState
        { players = [], currentIx = 0, drawPile = [], discardPile = [], burnedPiles = [],
          rng = initialGen, playDirection = 1, activeExtensions = [], finishedOrder = [], winners = [], turnCount = 0 }

      setupAction = newGame playerNames initialGen

      stateAfterDealing = execState setupAction initialDummyState

      (finalStatus, finalState) = runState gameLoopWithHistory stateAfterDealing

  putStrLn finalStatus
  return ()

--------------------------------------------------------------------------------
-- Step 4 
--------------------------------------------------------------------------------
playOneGameStep4 :: [Extension] -> IO ()
playOneGameStep4 exts = do
  initialGen <- newStdGen
  let playerNames = ["Player1", "Player2", "Player3"]

      initialDummyState = GameState
        { players = [], currentIx = 0, drawPile = [], discardPile = [], burnedPiles = [],
          rng = initialGen, playDirection = 1, activeExtensions = [], finishedOrder = [], winners = [], turnCount = 0 }

      setupAction = newGame playerNames initialGen

      stateAfterDealing = execState setupAction initialDummyState

      stateWithExts = stateAfterDealing { activeExtensions = exts }

      (finalStatus, finalState) = runState gameLoopWithHistory stateWithExts

  putStrLn finalStatus
  return ()
--------------------------------------------------------------------------------
-- Step 5 — Smart Player and Tournaments
--------------------------------------------------------------------------------
smartStrategy :: State GameState Deck
smartStrategy = do
  currentState <- get
  allPlayableCards <- getAllPlayableCards
  -- If there are no special playable cards, behave like basicStrategy
  if not (any isSpecialCard allPlayableCards)
    then basicStrategy
    else do
    let playersList = players currentState
        numPlayers = length playersList
        currentPlayerIx = currentIx currentState

        nextOpponent = playersList !! ((currentPlayerIx + 1) `mod` numPlayers)
        prevOpponent = playersList !! ((currentPlayerIx - 1 + numPlayers) `mod` numPlayers)

        isNextOpponentThreatening = getOpponentThreatScore nextOpponent <= 3
        isPrevOpponentThreatening = getOpponentThreatScore prevOpponent <= 3
        pileIsDangerous = length (discardPile currentState) >= 6
        topCard = listToMaybe (discardPile currentState)

        pileTopIsHigh = case topCard of
                          Just c  -> rank c >= R7
                          Nothing -> False
        noPlaySignal = [] :: Deck

    -- Steal card is found
    case findPlayableSteal allPlayableCards of
      -- Just stealCard is returned if next opponent is threatening
      Just stealCard | isNextOpponentThreatening -> return [stealCard] 

      _ -> case findPlayableReverse allPlayableCards of
             Just revCard | not isPrevOpponentThreatening && isNextOpponentThreatening -> return [revCard]

             _ -> case findPlayableReset allPlayableCards of
                    Just resetCard | (pileTopIsHigh || isNextOpponentThreatening) -> return [resetCard]

                    _ -> case findPlayableBurn allPlayableCards of
                           Just burnCard | pileIsDangerous -> return [burnCard]
                           _ -> do
                             -- Shedding same rank cards if possible 
                              -- (improved implementation from basicStrategySets)
                             let groupsByRank rs = [ filter ((== r) . rank) rs | r <- nub (map rank rs) ]
                                 rankGroups = groupsByRank allPlayableCards
                                 bestGroup = if null rankGroups then [] else maximumBy (comparing (\g -> (length g, rank (head g)))) rankGroups

                             if length bestGroup > 1
                               then return bestGroup
                               else case findHighestRankNonSpecial allPlayableCards of
                                      Just c  -> return [c]
                                      Nothing -> basicStrategy

-- Helper for smartStrategy
getAllPlayableCards :: State GameState Deck
getAllPlayableCards = do
  currentState <- get
  let playersList = players currentState
      playerIx = currentIx currentState
      currentPlayer = playersList !! playerIx
      currentPlayerHand = hand currentPlayer
      faceUpCards = faceUp currentPlayer
      topCard = listToMaybe (discardPile currentState)

  let handValid = validPlays topCard currentPlayerHand
      faceUpValid = validPlays topCard faceUpCards
      -- Prefer shedding face-up valid cards first when available
      availableCards = if not (null faceUpValid) then faceUpValid else handValid

  return availableCards

getOpponentThreatScore :: Player -> Int
getOpponentThreatScore player = 
    length (hand player) + length (faceUp player)

findPlayableSteal :: [Card] -> Maybe Card
findPlayableSteal playableCards = find isStealCard playableCards

findPlayableReverse :: [Card] -> Maybe Card
findPlayableReverse playableCards = find isReverseCard playableCards

findPlayableReset :: [Card] -> Maybe Card
findPlayableReset playableCards = find isResetCard playableCards

findPlayableBurn :: [Card] -> Maybe Card
findPlayableBurn playableCards = find isBurnCard playableCards


findHighestRankNonSpecial :: [Card] -> Maybe Card
findHighestRankNonSpecial [] = Nothing
findHighestRankNonSpecial xs =
  let nonSpecial = filter (not . isSpecialCard) xs
  in if null nonSpecial then Nothing else Just (minimumBy (comparing rank) nonSpecial)

-- Run a tournament of n independent games 
playTournament :: Int -> IO [(String, Int)]
playTournament n = do
  gens <- replicateM n newStdGen
  results <- mapM (\g -> do
    let playerNames = ["Player1", "Player2", "Player3"]

        initialDummyState = GameState
          { players = [], currentIx = 0, drawPile = [], discardPile = [], burnedPiles = [],
            rng = g, playDirection = 1, activeExtensions = [], finishedOrder = [], winners = [], turnCount = 0 }

        setupAction = newGame playerNames g

        stateAfterDealing = execState setupAction initialDummyState

        stratNames = ["Basic", "BasicSets", "Smart"]
        playersWithStrat = zipWith (\p s -> p { strategy = s }) (players stateAfterDealing) stratNames
        startState = stateAfterDealing { players = playersWithStrat }

        (gameLog, finalState) = runState gameLoop startState

    -- If game ended due to turn limit
    if "GAME ENDED DUE TO TURN LIMIT" `isInfixOf` gameLog
      then do
        -- Choose winner by smallest hand size
        let checkHandSize name = case find (\p -> pName p == name) (players finalState) of
                                   Just p -> length (hand p)
                                   Nothing -> 0
            starterNames = map pName playersWithStrat
            sizes = map (\nm -> (nm, checkHandSize nm)) starterNames
            -- Find player with smallest hand size
            (winnerName, _) = minimumBy (comparing snd) sizes
            -- Returns winner's strategy
            winnerStrategyMaybe = lookup winnerName (map (\p -> (pName p, strategy p)) playersWithStrat)
        return winnerStrategyMaybe
      else do
        -- Determine winner's name
        let winnerFromWinners = listToMaybe (winners finalState)
            -- Check if only one player remains if no winners recorded
            winnerFromRemaining = case players finalState of 
                        (p:_) | length (players finalState) == 1 -> Just (pName p)
                        _ -> Nothing
            winnerPlayerMaybe = winnerFromWinners `mplus` winnerFromRemaining

          -- Map player name to strategy using the players we assigned at start
            nameToStrategy = \p -> (pName p, strategy p)
            mapping = map nameToStrategy playersWithStrat
            winnerStrategyMaybe = winnerPlayerMaybe >>= (\nm -> lookup nm mapping)

        return winnerStrategyMaybe
    ) gens

  let validWinners = catMaybes results
      count name = length (filter (== name) validWinners)
      counts = [ ("Basic", count "Basic"), ("BasicSets", count "BasicSets"), ("Smart", count "Smart") ]
  return counts