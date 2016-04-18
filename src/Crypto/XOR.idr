module Crypto.XOR

import Crypto.Data
import Data.Vect
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

byteXor : Bits 8 -> Bits 8 -> Bits 8
byteXor = zipWith xorBit

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

xorCypher' : Char -> List (Bits 8) -> String
xorCypher' key bytes =
  let keyByte = vectSizer 8 O $ decimalToBinary $ cast $ ord key
      xord = map (byteXor keyByte) bytes
   in
      pack $ map (chr . fromInteger . binToInt) xord

xorCypher : Char -> String -> Maybe String
xorCypher key str =
  do dec <- hexStrToDecimal str
     let bytes = bitPartition 8 $ decimalToBinary dec
     pure $ xorCypher' key bytes

bruteForce : String -> IO ()
bruteForce x =
  case hexStrToDecimal x of
    Nothing => putStrLn $ "Unable to parse " ++ x ++ " as hex."
    Just dec => attempt possibleKeys $ bitPartition 8 $ decimalToBinary dec
  where
    possibleKeys : List Char
    possibleKeys = map chr $ enumFromTo 65 122
    attempt : List Char -> List (Bits 8) -> IO ()
    attempt [] x = pure ()
    attempt _ [] = putStrLn "No bytes!"
    attempt (key :: keys) bytes =
      let keyByte = vectSizer 8 O $ decimalToBinary $ cast $ ord key
          xord = map (byteXor keyByte) bytes
          result = pack $ map (chr . fromInteger . binToInt) xord
       in
        do putStrLn $ (show key) ++ "=" ++ result
           attempt keys bytes
