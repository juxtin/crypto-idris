module Crypto.Data

import Data.Fin
import Data.Vect
%access public export

data BinaryDigit = O | I
%name BinaryDigit bit

Bits : Nat -> Type
Bits n = Vect n BinaryDigit

bitToDecimal : BinaryDigit -> Integer
bitToDecimal O = 0
bitToDecimal I = 1

data HexDigit = H0 | H1 | H2 | H3 | H4 | H5 | H6 | H7 | H8 | H9 | HA | HB | HC | HD | HE | HF
%name HexDigit hex

hexDigitToInt : HexDigit -> Integer
hexDigitToInt H0 = 0
hexDigitToInt H1 = 1
hexDigitToInt H2 = 2
hexDigitToInt H3 = 3
hexDigitToInt H4 = 4
hexDigitToInt H5 = 5
hexDigitToInt H6 = 6
hexDigitToInt H7 = 7
hexDigitToInt H8 = 8
hexDigitToInt H9 = 9
hexDigitToInt HA = 10
hexDigitToInt HB = 11
hexDigitToInt HC = 12
hexDigitToInt HD = 13
hexDigitToInt HE = 14
hexDigitToInt HF = 15

finToHex : Fin 16 -> HexDigit
finToHex n =
  case finToInteger n of
    0 => H0
    1 => H1
    2 => H2
    3 => H3
    4 => H4
    5 => H5
    6 => H6
    7 => H7
    8 => H8
    9 => H9
    10 => HA
    11 => HB
    12 => HC
    13 => HD
    14 => HE
    15 => HF

hexDigitToChar : HexDigit -> Char
hexDigitToChar H0 = '0'
hexDigitToChar H1 = '1'
hexDigitToChar H2 = '2'
hexDigitToChar H3 = '3'
hexDigitToChar H4 = '4'
hexDigitToChar H5 = '5'
hexDigitToChar H6 = '6'
hexDigitToChar H7 = '7'
hexDigitToChar H8 = '8'
hexDigitToChar H9 = '9'
hexDigitToChar HA = 'A'
hexDigitToChar HB = 'B'
hexDigitToChar HC = 'C'
hexDigitToChar HD = 'D'
hexDigitToChar HE = 'E'
hexDigitToChar HF = 'F'

BinList : Type
BinList = List BinaryDigit
%name BinList bits

binToDecimal : BinList -> Integer
binToDecimal xs =
  binToDecimal' 0 Z $ reverse xs
  where
    binToDecimal' : (acc : Integer) -> (pos : Nat) -> BinList -> Integer
    binToDecimal' acc _ [] = acc
    binToDecimal' acc pos (bit :: bits) =
      let n = bitToDecimal bit in
        binToDecimal' (acc + (n * (2 `pow` pos))) (pos + 1) bits

binToNat : BinList -> Nat
binToNat = cast . binToDecimal

binToInt : Bits n -> Integer
binToInt = binToInt' . reverse
  where
    binToInt' : Bits n -> Integer
    binToInt' [] = 0
    binToInt' (x :: xs) =
      (+) (bitToDecimal x) $ 2 * (binToInt' xs)

partial
byteMaxSize : (n : Nat) -> binToInt (replicate n I) = (2 `pow` n) - 1
byteMaxSize (S (S (S (S Z)))) = Refl -- 4
byteMaxSize (S (S (S (S (S (S Z)))))) = Refl -- 6
byteMaxSize (S (S (S (S (S (S (S Z))))))) = Refl -- 7

binToFin : Bits n -> Fin $ 2 `pow` n
binToFin {n} x =
  case natToFin (cast $ binToInt x) (2 `pow` n) of
    Just fin => fin
    Nothing => believe_me 0 -- this should be unreachable anyway, but the
                            -- believe_me is necessary because the compiler
                            -- claims that FZ is not strictly less than (pow 2 n),
                            -- but obviously it is.

Byte : Type
Byte = Vect 8 BinaryDigit

isHexChar : Char -> Bool
isHexChar x =
  isDigit x || (x `elem` hexChars)
  where
    hexChars : List Char
    hexChars = unpack "ABCDEF"

isHexStr : String -> Bool
isHexStr x = all isHexChar $ unpack x

Hex : Type
Hex = List HexDigit

parseHexChar : Char -> Maybe HexDigit
parseHexChar x =
  case x of
    '0' => Just H0
    '1' => Just H1
    '2' => Just H2
    '3' => Just H3
    '4' => Just H4
    '5' => Just H5
    '6' => Just H6
    '7' => Just H7
    '8' => Just H8
    '9' => Just H9
    'A' => Just HA
    'B' => Just HB
    'C' => Just HC
    'D' => Just HD
    'E' => Just HE
    'F' => Just HF
    _   => Nothing

parseHex : String -> Maybe Hex
parseHex str =
  let x = toUpper str in
    if isHexStr x
      then Just $ mapMaybe parseHexChar $ unpack x
      else Nothing

hexToDecimal : Hex -> Integer
hexToDecimal hex =
  let digits = reverse hex in
    hexToDecimal' 0 Z digits
  where
    hexToDecimal' : (acc : Integer) -> (pos : Nat) -> Hex -> Integer
    hexToDecimal' acc _ [] = acc
    hexToDecimal' acc pos (hex::hexs) =
      let n = hexDigitToInt hex
          multiplier = 16 `pow` pos
          newAcc = (acc + (n * multiplier)) in
        hexToDecimal' newAcc (pos + 1) hexs

hexStrToDecimal : String -> Maybe Integer
hexStrToDecimal s =
  do hex <- parseHex s
     return $ hexToDecimal hex

hexEx1 : hexStrToDecimal "1D9" = Just 473
hexEx1 = Refl

hexEx2 : hexStrToDecimal "80E1" = Just 32993
hexEx2 = Refl

hexEx3 : hexStrToDecimal "10CE" = Just 4302
hexEx3 = Refl

hexEx4 : hexStrToDecimal "877HOTLINEBLING" = Nothing
hexEx4 = Refl

isEven : Integer -> Bool
isEven = (==0) . (flip mod 2)

decimalToBinary' : (acc : List BinaryDigit) -> Integer -> BinList
decimalToBinary' acc 0 = O :: acc
decimalToBinary' acc 1 = I :: acc
decimalToBinary' acc n =
  if isEven n
  then decimalToBinary' (O :: acc) (n `div` 2)
  else decimalToBinary' (I :: acc) (n `div` 2)

binListShow : BinList -> String
binListShow [] = ""
binListShow (x :: xs) =
  case x of
    O => "0" ++ binListShow xs
    I => "1" ++ binListShow xs

decimalToBinary : Integer -> BinList
decimalToBinary = decimalToBinary' []

HexByte : Type
HexByte = Vect 4 BinaryDigit

||| Constructs a vector of size n given a list. Intended to be used with bytes,
||| so elements are added (as `def`) or dropped from the beginning if necessary.
vectSizer : (n : Nat) -> (def : a) -> List a -> Vect n a
vectSizer n def xs =
  reverse $ vectSizer' n def $ reverse xs
  where
    vectSizer' Z def xs = []
    vectSizer' (S k) def [] = def :: vectSizer' k def []
    vectSizer' (S k) def (x :: xs) = x :: vectSizer' k def xs

hexToBinary : HexDigit -> HexByte
hexToBinary x =
  let n = hexDigitToInt x in
     vectSizer 4 O $ decimalToBinary n

-- hex index is 4 bits
-- b64 index is 6 bits
-- LCM is 12 bits, i.e. 3 hex -> 2 b64

base64Chars : Vect 64 Char
base64Chars = fromList $ unpack
  $  "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  ++ "abcdefghijklmnopqrstuvwxyz"
  ++ "0123456789+/"

||| Divides the given list into a list of lists of (up to) `size` in length.
sizePartition : (size : Nat) -> List a -> List $ List a
sizePartition size [] = []
sizePartition size bits = (take size bits) :: (sizePartition size $ drop size bits)

||| Divides the given BinList into a list of Byte vectors which are all
||| `n` in length. Pads the BinList with initial O's if necessary.
bitPartition : (n : Nat) -> BinList -> List $ Bits n
bitPartition size bits =
  let padding = getPadding size bits
      padded = padding ++ bits in
    map (vectSizer size O) $ sizePartition size padded
  where
    getPadding : Nat -> BinList -> BinList
    getPadding size bits =
      let smallChunk = (length bits) `mod` size
          deficit = size `minus` smallChunk in
        replicate deficit O

base64Index : Bits 6 -> Char
base64Index bits =
  let idx = binToFin bits in
    index idx base64Chars

hexToBase64' : List $ Bits 4 -> List $ Bits 6
hexToBase64' [] = []
hexToBase64' bits =
  let n = map binToInt bits in
    bitPartition 6 $ concat $ map decimalToBinary n

integerToBase64' : Integer -> List $ Bits 6
integerToBase64' x =
  let bits = decimalToBinary x in
    bitPartition 6 bits

integerToBase64 : Integer -> String
integerToBase64 = pack . map base64Index . integerToBase64'

hexToBase64 : String -> Maybe String
hexToBase64 x =
  case hexStrToDecimal x of
    Nothing => Nothing
    Just n => Just $ integerToBase64 n

byteToHex : BinList -> Maybe HexDigit
byteToHex bits =
  do n <- natToFin (cast $ binToDecimal bits) 16
     return $ finToHex n

binToHex : BinList -> List HexDigit
binToHex bits =
  let bytes = bitPartition 4 bits in
      map (finToHex . binToFin) bytes

hexToASCII' : (Char, Char) -> Maybe String
hexToASCII' (a, b) =
  let str = pack $ the (List Char) [a, b] in
    do n <- hexStrToDecimal str
       let bits = decimalToBinary n
       let charIdx = binToDecimal bits
       let char = chr $ fromInteger charIdx
       pure $ singleton char

hexToASCII : String -> Maybe String
hexToASCII x =
  if not $ isHexStr x then Nothing
  else let chars = unpack x
           pairs = pairify chars
           chars = mapMaybe hexToASCII' pairs in
         return $ concat chars
  where
    pairify : List Char -> List (Char, Char)
    pairify [] = []
    pairify (y :: []) = [('0', y)]
    pairify (y :: (z :: xs)) = (y, z) :: pairify xs

asciiToHex : String -> String
asciiToHex x =
  let chars = unpack x
      bytes = concat $ map (bitPartition 4 . decimalToBinary . cast . ord) chars
      hexes = map (finToHex . binToFin) bytes
   in
    pack $ map hexDigitToChar hexes

asciiRoundTrip : String -> Maybe String
asciiRoundTrip = hexToASCII . asciiToHex
