module Crypto.XOR

import Crypto.Data
%access public export

xorBit : BinaryDigit -> BinaryDigit -> BinaryDigit
xorBit O O = O
xorBit I I = O
xorBit _ _ = I

||| Given two lists of potentially unequal length, return a pair of both lists
||| with the smaller one padded to match the length of the larger.
equalizeLength : (pad : a) -> List a -> List a -> (List a, List a)
equalizeLength pad xs ys =
  let longest = max (length xs) (length ys)
      padx = replicate (longest `minus` (length xs)) pad
      pady = replicate (longest `minus` (length ys)) pad in
    ((padx ++ xs), (pady ++ ys))

xor : BinList -> BinList -> BinList
xor bitsA bitsB =
  let (xs, ys) = equalizeLength O bitsA bitsB in
    xor' xs ys
  where
    xor' : BinList -> BinList -> BinList
    xor' [] [] = []
    xor' [] (x :: xs) = x :: xor' [] xs
    xor' (x :: xs) [] = x :: xor' xs []
    xor' (x :: xs) (y :: ys) = xorBit x y :: xor' xs ys

fixedXOR : String -> String -> Maybe String
fixedXOR x y =
  let (bitx, bity) = (toUpper x, toUpper y) in
    if not $ isHexStr bitx && isHexStr bity then Nothing
    else do hexA <- hexStrToDecimal bitx
            hexB <- hexStrToDecimal bity
            binA <- Just $ decimalToBinary hexA
            binB <- Just $ decimalToBinary hexB
            xord <- Just $ xor binA binB
            hexChars <- Just $ binToHex xord
            return $ pack $ map hexDigitToChar hexChars

letters : String -> List String
letters = map singleton . unpack

xorCypher : (cypher : Char) -> String -> Maybe String
xorCypher cypher x =
  if not $ isHexStr x && isHexChar cypher then Nothing
  else do return $ concat $ mapMaybe (fixedXOR $ singleton cypher) $ letters x

bruteForce : String -> IO ()
bruteForce x =
  let hex = toUpper x in
    attempt hex possibleKeys
  where
    possibleKeys : List Char
    possibleKeys = map chr $ enumFromTo 65 122
    attempt : String -> List Char -> IO ()
    attempt x [] = pure ()
    attempt x (key::keys) =
      case xorCypher key x of
        Nothing => do putStrLn $ "failed to xorCypher with " ++ (show key)
                      attempt x keys
        Just res => case hexToASCII res of
                      Nothing => do putStrLn $ "failed to hexToASCII with " ++ res
                                    attempt x keys
                      Just str => do putStrLn $ (show key) ++ "= " ++ str
                                     attempt x keys

