module Crypto.Heuristics

lettersByFrequency : String -> List Char
lettersByFrequency str =
  map snd $ reverse $ sort $ foldl update [] (unpack $ toUpper str)
  where
    inc : Char -> (Nat, Char) -> (Nat, Char)
    inc this pair@(freq, char) = if this == char
                                   then (freq + 1, char)
                                   else pair
    update : List (Nat, Char) -> Char -> List (Nat, Char)
    update pairs this =
      let letters = map snd pairs in
        if this `elem` letters
          then map (inc this) pairs
          else (1, this) :: pairs

letterRanks : List Char -> List (Char, Nat)
letterRanks chars = zip chars (map S $ natRange $ length chars)

stringRanks : String -> List (Char, Nat)
stringRanks = letterRanks . lettersByFrequency

idealRanks : List (Char, Nat)
idealRanks =
  let letters = unpack "ETAOINSHRDLU"
      ranks = map S (natRange $ length letters)
   in
    zip letters ranks

letterRank : List (Char, Nat) -> Char -> Nat
letterRank ranks this =
  case getPair ranks this of
    Nothing => length ranks + 1
    Just rank => rank
  where
    getPair : List (Char, Nat) -> Char -> Maybe Nat
    getPair [] _ = Nothing
    getPair ((c, rank) :: ps) this = if c == this then Just rank else getPair ps this

scoreText : String -> Integer
scoreText str =
     foldl score 0 ranks
  where
    ranks : List (Char, Nat)
    ranks = stringRanks str
    score : Nat -> (Char, Nat) -> Integer
    score acc (char, rank) =
      let target = letterRank idealRanks char
          gtr = cast $ maximum target rank
          smlr = cast $ minimum target rank
      in
        acc - gtr - smlr

{-
  1. start with 'E'
    1a. if 'E' is the most common letter, increment the score by 1
    1b. if it's the second most common letter, increment by 1/2
    3b. if it's the third most common letter, by 1/3, etc
  2. continue with 'T'
    2b. if it's the second most common letter, increment by 1
    2b. if it's the third most common letter, increment by 1/2

  in other words, take a pair of (Char, Nat) from the expected order
  grab the corresponding
-}


letterScore : String -> Integer
letterScore x =
  let chars = filter (/= ' ') $ unpack $ toUpper x in
    ?huh
