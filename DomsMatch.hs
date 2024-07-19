{- 
   Jihye Bae

   COM2108 Functional Programming
   Grading Assignment

   Implements fives-and-threes dominos game with two players, simplePlayer and smartPlayer.
   smartPlayer follows three different strategies based on the game state.

   Stub with types provided by Emma Norling (October 2023).
-}

module DomsMatch where
    import System.Random
    import Data.List
    import Data.Ord (comparing)


    -- types used in this module
    type Domino = (Int, Int) -- a single domino
    {- Board data type: either an empty board (InitState) or the current state as represented by
        * the left-most domino (such that in the tuple (x,y), x represents the left-most pips)
        * the right-most domino (such that in the tuple (x,y), y represents the right-most pips)
        * the history of moves in the round so far
     -}
    data Board = InitState | State Domino Domino History deriving (Eq, Show)
    {- History should contain the *full* list of dominos played so far, from leftmost to
       rightmost, together with which player played that move and when they played it
     -}
    type History = [(Domino, Player, MoveNum)]
    data Player = P1 | P2 deriving (Eq, Show)
    data End = L | R deriving (Eq, Show)
    type Scores = (Int, Int) -- P1’s score, P2’s score
    type MoveNum = Int
    type Hand = [Domino]
    {- DomsPlayer is a function that given a Hand, Board, Player and Scores will decide
       which domino to play where. The Player information can be used to "remember" which
       moves in the History of the Board were played by self and which by opponent
     -}
    type DomsPlayer = Hand -> Board -> Player -> Scores -> (Domino, End)

    {- domSet: a full set of dominoes, unshuffled -}
    domSet = [ (l,r) | l <- [0..6], r <- [0..l] ]

    {- shuffleDoms: returns a shuffled set of dominoes, given a number generator
       It works by generating a random list of numbers, zipping this list together
       with the ordered set of dominos, sorting the resulting pairs based on the random
       numbers that were generated, then outputting the dominos from the resulting list.
     -}
    shuffleDoms :: StdGen -> [Domino]
    shuffleDoms gen = [ d | (r,d) <- sort (zip (randoms gen :: [Int]) domSet)]

    {- domsMatch: play a match of n games between two players,
        given a seed for the random number generator
       input: number of games to play, number of dominos in hand at start of each game,
              target score for each game, functions to determine the next move for each
              of the players, seed for random number generator
       output: a pair of integers, indicating the number of games won by each player
     -}
    domsMatch :: Int -> Int -> Int -> DomsPlayer -> DomsPlayer -> Int -> (Int, Int)
    domsMatch games handSize target p1 p2 seed
        = domsGames games p1 p2 (mkStdGen seed) (0, 0)
          where
          domsGames 0 _  _  _   wins               = wins
          domsGames n p1 p2 gen (p1_wins, p2_wins)
            = domsGames (n-1) p1 p2 gen2 updatedScore
              where
              updatedScore
                | playGame handSize target p1 p2 (if odd n then P1 else P2) gen1 == P1 = (p1_wins+1,p2_wins)
                | otherwise                                            = (p1_wins, p2_wins+1)
              (gen1, gen2) = split gen
              {- Note: the line above is how you split a single generator to get two generators.
                 Each generator will produce a different set of pseudo-random numbers, but a given
                 seed will always produce the same sets of random numbers.
               -}

    {- playGame: play a single game (where winner is determined by a player reaching
          target exactly) between two players
       input: functions to determine the next move for each of the players, player to have
              first go, random number generator 
       output: the winning player
     -}
    playGame :: Int -> Int -> DomsPlayer -> DomsPlayer -> Player -> StdGen -> Player
    playGame handSize target p1 p2 firstPlayer gen
        = playGame' p1 p2 firstPlayer gen (0, 0)
          where
          playGame' p1 p2 firstPlayer gen (s1, s2)
            | s1 == target = P1
            | s2 == target = P2
            | otherwise
                = let
                      newScores = playDomsRound handSize target p1 p2 firstPlayer currentG (s1, s2)
                      (currentG, nextG) = split gen
                  in
                  playGame' p1 p2 (if firstPlayer == P1 then P2 else P1) nextG newScores

    {- playDomsRound: given the starting hand size, two dominos players, the player to go first,
        the score at the start of the round, and the random number generator, returns the score at
        the end of the round.
        To complete a round, turns are played until either one player reaches the target or both
        players are blocked.
     -}
    playDomsRound :: Int -> Int -> DomsPlayer -> DomsPlayer -> Player -> StdGen -> (Int, Int) -> (Int, Int)
    playDomsRound handSize target p1 p2 first gen scores
        = playDomsRound' p1 p2 first (hand1, hand2, InitState, scores)
          where
          -- shuffle the dominoes and generate the initial hands
          shuffled = shuffleDoms gen
          hand1 = take handSize shuffled
          hand2 = take handSize (drop handSize shuffled)
          {- playDomsRound' recursively alternates between each player, keeping track of the game state
             (each player's hand, the board, the scores) until both players are blocked -}
          playDomsRound' p1 p2 turn gameState@(hand1, hand2, board, (score1,score2))
            | (score1 == target) || (score2 == target) || (p1_blocked && p2_blocked) = (score1,score2)
            | turn == P1 && p1_blocked = playDomsRound' p1 p2 P2 gameState
            | turn == P2 && p2_blocked = playDomsRound' p1 p2 P1 gameState
            | turn == P1               = playDomsRound' p1 p2 P2 newGameState
            | otherwise                = playDomsRound' p1 p2 P1 newGameState
              where
              p1_blocked = blocked hand1 board
              p2_blocked = blocked hand2 board
              (domino, end)          -- get next move from appropriate player
                  | turn == P1 = p1 hand1 board turn (score1, score2)
                  | turn == P2 = p2 hand2 board turn (score1, score2)
                                     -- attempt to play this move
              maybeBoard             -- try to play domino at end as returned by the player
                  | turn == P1 && not (domInHand domino hand1) = Nothing -- can't play a domino you don't have!
                  | turn == P2 && not (domInHand domino hand2) = Nothing
                  | otherwise = playDom turn domino board end
              newGameState           -- if successful update board state (exit with error otherwise)
                 | maybeBoard == Nothing = error ("Player " ++ show turn ++ " attempted to play an invalid move.")
                 | otherwise             = (newHand1, newHand2, newBoard,
                                              (limitScore score1 newScore1, limitScore score2 newScore2))
              (newHand1, newHand2)   -- remove the domino that was just played
                 | turn == P1 = (hand1\\[domino], hand2)
                 | turn == P2 = (hand1, hand2\\[domino])
              score = scoreBoard newBoard (newHand1 == [] || newHand2 == [])
              (newScore1, newScore2) -- work out updated scores
                 | turn == P1 = (score1+score,score2)
                 | otherwise  = (score1,score2+score)
              limitScore old new     -- make sure new score doesn't exceed target
                 | new > target = old
                 | otherwise    = new
              Just newBoard = maybeBoard -- extract the new board from the Maybe type

    {- domInHand: check if a particular domino is contained within a hand -}
    domInHand :: Domino -> Hand -> Bool
    domInHand (l,r) hand = [ 1 | (dl, dr) <- hand, (dl == l && dr == r) || (dr == l && dl == r) ] /= []

    scoreBoard :: Board -> Bool -> Int
    scoreBoard InitState _ = 0
    scoreBoard (State (l1,l2) (r1,r2) _) lastTile
      | lastTile  = pipTotal (leftEnd + rightEnd) + 1 -- 'chips out' then score one point
      | otherwise = pipTotal (leftEnd + rightEnd)
        where
          leftEnd | l1 == l2  = 2*l1
                  | otherwise = l1
          rightEnd | r1 == r2  = 2*r2
                   | otherwise = r2
          pipTotal pt
            | pt == 3   = 1 -- One 3
            | pt == 5   = 1 -- One 5
            | pt == 6   = 2 -- Two 3s
            | pt == 9   = 3 -- Three 3s
            | pt == 10  = 2 -- Two 5s
            | pt == 12  = 4 -- Four 3s
            | pt == 15  = 8 -- Five 3s and Three 5s
            | pt == 18  = 6 -- Six 3s
            | pt == 20  = 4 -- Four 5s
            | otherwise = 0 -- Not a multiple of 5 or 3

    {- canPlay: domino can be played at the given end the board -}
    canPlay :: Domino -> End -> Board -> Bool
    canPlay (d1,d2) _ InitState = True -- Any domino can be played
    canPlay (d1,d2) L (State (l1,l2) (r1,r2) _) | d1 == l1 || d2 == l1 = True
                                                | otherwise            = False
    canPlay (d1,d2) R (State (l1,l2) (r1,r2) _) | d1 == r2 || d2 == r2 = True
                                                | otherwise            = False

    {- blocked: no domino in the hand that can be played on the board -}
    blocked :: Hand -> Board -> Bool
    blocked [] _ = True -- If Hand is empty then True
    blocked _ InitState = False -- If board initState, not blocked
    blocked (currentDomino:restOfTheDominoes) (State (l1,l2) (r1,r2) history)
      | canPlay currentDomino L (State (l1,l2) (r1,r2) history)
        || canPlay currentDomino R (State (l1,l2) (r1,r2) history) = False
      | otherwise = blocked restOfTheDominoes (State (l1,l2) (r1,r2) history)

    {- playDom : play the domino at the given end if it is possible to play it or nothing -}
    playDom :: Player -> Domino -> Board -> End -> Maybe Board
    playDom p (d1, d2) InitState _ = Just (State (d1, d2) (d1, d2) [((d1, d2), p, 1)])
    playDom p (d1,d2) (State (l1,l2) (r1,r2) history) L
      | canPlay (d1,d2) L (State (l1,l2) (r1,r2) []) && d1 == l1
        = Just (State (d2,d1) (r1, r2) (((d2,d1), p, length history + 1):history))
      | canPlay (d1,d2) L (State (l1,l2) (r1,r2) []) && d2 == l1
        = Just (State (d1,d2) (r1, r2) (((d1,d2), p, length history + 1):history))
      | otherwise = Nothing
    playDom p (d1,d2) (State (l1,l2) (r1,r2) history) R
      | canPlay (d1,d2) R (State (l1,l2) (r1,r2) []) && d1 == r2
        = Just (State (l1,l2) (d1, d2) (history ++ [((d1,d2), p, length history + 1)]))
      | canPlay (d1,d2) R (State (l1,l2) (r1,r2) []) && d2 == r2
        = Just (State (l1,l2) (d2, d1) (history ++ [((d2,d1), p, length history + 1)]))
      | otherwise = Nothing

    {- possPlays : return all the Dominos which may be played at the left End and all those that may be played at the right End-}
    possPlays :: Hand -> Board -> ([Domino],[Domino])
    possPlays [] _ = ([], [])
    possPlays hand InitState = (hand, hand)
    possPlays (currentDomino:restOfTheDominoes) board
      | canPlay currentDomino L board && canPlay currentDomino R board = (currentDomino:leftDominos, currentDomino:rightDominos)
      | canPlay currentDomino L board = (currentDomino:leftDominos, rightDominos)
      | canPlay currentDomino R board = (leftDominos, currentDomino:rightDominos)
      | otherwise = (leftDominos, rightDominos)
        where
          (leftDominos, rightDominos) = possPlays restOfTheDominoes board

    {- simplePlayer : returns a tuple that indicating the domino to be played and the end at which to play it -}
    simplePlayer :: DomsPlayer
    simplePlayer (currentDomino:_) InitState _ _ = (currentDomino, L)  -- Assumes there is at least one domino in the hand
    simplePlayer (currentDomino:restOfTheDominoes) (State (l1, l2) (r1, r2) history) _ _ =
      case possPlays (currentDomino:restOfTheDominoes) (State (l1, l2) (r1, r2) history) of
        (currentDomino:leftDominos, _) -> (currentDomino, L)
        (_, currentDomino:rightDominos) -> (currentDomino, R)

    {- Strategy1, highestScoringDomino : Play domino which has the highest score -}
    highestScoringDomino :: DomsPlayer
    highestScoringDomino hand InitState player score = (highestScore, L)
      where
        highestScore = maximumBy (comparing (\(d1, d2) -> d1 + d2)) hand

    highestScoringDomino hand (State (l1, l2) (r1, r2) history) player _
      | canPlay (d1, d2) L (State (l1, l2) (r1, r2) history) && canPlay (d1, d2) R (State (l1, l2) (r1, r2) history)
        && (d2 == l1 || r2 == d1) = ((d1, d2), dominoEnd)
      | canPlay (d1, d2) L (State (l1, l2) (r1, r2) history) && canPlay (d1, d2) R (State (l1, l2) (r1, r2) history)
        && (d1 == l1 || r2 == d2) = ((d2, d1), dominoEnd)
      | canPlay (d1, d2) L (State (l1, l2) (r1, r2) history) && (l1 == d2) = ((d1, d2), L)
      | canPlay (d1, d2) L (State (l1, l2) (r1, r2) history) && (d1 == l1) = ((d2, d1), L)
      | canPlay (d1, d2) R (State (l1, l2) (r1, r2) history) && (r2 == d1) = ((d1, d2), R)
      | canPlay (d1, d2) R (State (l1, l2) (r1, r2) history) && (r2 == d2) = ((d2, d1), R)
      | otherwise = ((d1, d2), dominoEnd)
      where
        (d1, d2) = maximumBy (comparing (\(dom1, dom2) ->
              max
                (scoreBoard (case playDom player (dom1, dom2) (State (l1, l2) (r1, r2) history) L of
                              Just board -> board
                              Nothing -> InitState) True)
                (scoreBoard (case playDom player (dom1, dom2) (State (l1, l2) (r1, r2) history) R of
                              Just board -> board
                              Nothing -> InitState) True))) hand

        -- If player has multiple choices for dominos then choose the end that has the highest score
        dominoEnd | scoreBoard (case playDom player (d1,d2) (State (l1, l2) (r1, r2) history) L of
                                  Just board -> board
                                  Nothing -> InitState) True >
                    scoreBoard (case playDom player (d1,d2) (State (l1, l2) (r1, r2) history) R of
                                  Just board -> board
                                  Nothing -> InitState) True = L
                  | otherwise = R


    {- Strategy2, blockingPlayer : Block the opponenent's domino -}
    blockingPlayer :: DomsPlayer
    -- No need to block in InitState so return the domino that has the highest score
    blockingPlayer (currentDomino:restOfTheDominoes) InitState player _ = (highestScore, L)
      where
        highestScore = maximumBy (comparing (\(d1, d2) -> d1 + d2)) (currentDomino:restOfTheDominoes)

    blockingPlayer (currentDomino:restOfTheDominoes) (State (l1, l2) (r1, r2) history) player _ = ((d1, d2), dominoEnd)
      where
        board = State (l1, l2) (r1, r2) history
        -- List all the dominoes that can play
        possibilities = filter (\(d1, d2) -> canPlay (d1, d2) L board || canPlay (d1, d2) R board) (currentDomino:restOfTheDominoes)
        -- domino history for opponent
        dominoHistory = map (\((d1, d2), _, _) -> (d1, d2)) $ filter (\(_, p, _) -> p /= player) history
        -- Guess Opponenet domino (the opponent's dominos that can play)
        guessDomino = (possibilities \\ dominoHistory) \\ filter (`domInHand` (currentDomino:restOfTheDominoes)) possibilities
        -- Looking for a domino in hand that can block guessDomino
        (d1, d2) = case find (\(d1, d2) -> blocked (currentDomino:restOfTheDominoes) board) guessDomino of
                      Just (d1, d2) -> (d1, d2)
                      -- If no blocking domino is found, play the domino in hand which satisfies canPlay
                      Nothing -> let validDominos = filter (\domino -> domInHand domino (currentDomino:restOfTheDominoes)
                                                              && (canPlay domino L board || canPlay domino R board)) domSet
                                  in head validDominos

        dominoEnd
          | canPlay (d1, d2) L board && canPlay (d1, d2) R board =
            if scoreBoard (case playDom player (d1,d2) board L of
                              Just board -> board
                              Nothing -> InitState) True >
               scoreBoard (case playDom player (d1,d2) board R of
                              Just board -> board
                              Nothing -> InitState) True
            then L else R
          | canPlay (d1, d2) L board = L
          | otherwise = R


    {- Strategy3, particularSpot : using the domino that has a majority of one particular spot value -}
    particularSpot :: DomsPlayer
    particularSpot (currentDomino:restOfTheDominoes) board player _
      | board == InitState = ((d1, d2), L)
      | canPlay (d1, d2) L board && canPlay (d1, d2) R board && (d2 == l1 || r2 == d1) = ((d1, d2), dominoEnd)
      | canPlay (d1, d2) L board && canPlay (d1, d2) R board && (d1 == l1 || r2 == d2) = ((d2, d1), dominoEnd)
      | canPlay (d1, d2) L board && (l1 == d2) = ((d1, d2), L)
      | canPlay (d1, d2) L board && (d1 == l1) = ((d2, d1), L)
      | canPlay (d1, d2) R board && (r2 == d1) = ((d1, d2), R)
      | canPlay (d1, d2) R board && (r2 == d2) = ((d2, d1), R)
      | otherwise = ((d1, d2), dominoEnd)
        where
          (State (l1, l2) (r1, r2) history) = board
          -- Checking all the spots in domino
          spotsValue = [d1 | (d1, _) <- (currentDomino:restOfTheDominoes)] ++ [d2 | (_, d2) <- (currentDomino:restOfTheDominoes)]
          -- Count the dominoes
          countDomino = map (\value -> (value, length $ filter (\(d1, d2) -> d1 == value || d2 == value) (currentDomino:restOfTheDominoes))) spotsValue
          -- Finding majority of particular spot
          majoritySpot = fst $ maximumBy (comparing snd) countDomino
          -- List of dominoes that has majority of particular spot
          majorityDominoes = filter (\(d1, d2) -> d1 == majoritySpot || d2 == majoritySpot) (currentDomino:restOfTheDominoes)
          -- finding double domino in majorityDominoes
          doubleDomino = filter (\(d1, d2) -> (d1 == majoritySpot || d2 == majoritySpot) && d1 == d2) (currentDomino:restOfTheDominoes)

          (d1, d2) =
            case find (\(dom1, dom2) -> (canPlay (dom1, dom2) L board) || (canPlay (dom1, dom2) R board)) doubleDomino of
              Just (d1, d2) -> (d1, d2)
              Nothing ->
                case find (\(dom1, dom2) -> (canPlay (dom1, dom2) L board) || (canPlay (dom1, dom2) R board)) majorityDominoes of
                  Just (d1, d2) -> (d1, d2)
                  Nothing ->
                    let validDominos = filter (\domino -> domInHand domino (currentDomino:restOfTheDominoes)
                                                  && (canPlay domino L board || canPlay domino R board)) domSet
                    in head validDominos

          dominoEnd | canPlay (d1, d2) L board && canPlay (d1, d2) R board = if scoreBoard (case playDom player (d1,d2) board L of
                                                                                                Just board -> board
                                                                                                Nothing -> InitState) True >
                                                                                scoreBoard (case playDom player (d1,d2) board R of
                                                                                                Just board -> board
                                                                                                Nothing -> InitState) True
                                                                              then L else R
                    | canPlay (d1, d2) L board = L
                    | otherwise = R

    smartPlayer :: DomsPlayer
    smartPlayer hand InitState player score
      -- Check domino (4,5) exists
      | elem (4,5) hand || elem (5,4) hand = ((4,5), L)
      | otherwise = highestScoringDomino hand InitState player score

    smartPlayer hand (State (l1, l2) (r1, r2) history) player score
      -- Player has weak hand, low variety of number, or opponent is getting close in the end game then use blockingPlayer Strategy
      | weakHand || opponentNearEnd = blockingPlayer hand (State (l1, l2) (r1, r2) history) player score
      -- Condition of using particularSpot Strategy
      | any (\x -> length (filter (\(a, b) -> a == x || b == x) hand) >= 4) allNumbers   = particularSpot hand (State (l1, l2) (r1, r2) history) player score
      -- Default Strategy : highestScoringDomino strategy
      | otherwise = highestScoringDomino hand (State (l1, l2) (r1, r2) history) player score
      where
        weakHand = length (nub (concatMap (\(a, b) -> [a, b]) hand)) <= 3
        handSize = length hand
        opponentNearEnd = handSize - length (opponentHistory player history) <= 2
        allNumbers = nub (concatMap (\(a, b) -> [a, b]) hand)

    opponentHistory :: Player -> History -> History
    opponentHistory player history = filter (\(_, p, _) -> p /= player) history