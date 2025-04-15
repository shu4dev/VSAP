
{-
  Simple as possible file system: (inefficient, only for small devices)
  List of block groups (BG), each of which is a file or empty spaces.
  A BG begins with a 64-bit/8-byte size in bytes, then the name, then the data
  The size includes the initial 8 bytes and the null-terminated name
  For an empty space, the name is empty, meaning only the null byte.
-}

module SimpleFS where

import Data.Word
import Data.Int
import Data.Bits
import Data.Char
import Data.List (intercalate)
import Control.Monad (when)
import System.Random
import qualified Data.Array as Array

-- Device type definition
data Device = Device { 
  name :: String,
  bs :: Int64,
  nb :: Int64,
  r :: Int64 -> [Int],
  w :: Int64 -> [Int] -> IO ()
}

{-
  1. assert: every write operation in this program writes device.bs bytes,
     every read operation after calling format reads device.bs bytes
  2. assert: the name of every file fits in device.bs - 9 (see new_file)
  3. assert: unless there are errors, every file written is accessible
     until a matching delete_file (or forever).
-}

checkInvariant1 :: Int64 -> [Int] -> IO ()
checkInvariant1 bs lst = 
  if fromIntegral (length lst) == bs 
  then return () 
  else error "Invariant 1 violated"

checkInvariant2 :: Int64 -> [Int] -> IO ()
checkInvariant2 bs name =
  if length name <= fromIntegral bs - 9
  then return ()
  else error "Invariant 2 violated"

-- Generic functions for groups of bytes
getn :: [Int] -> Int -> [Int]  -- get n bytes from the list
getn lst n
  | n <= 0    = []
  | otherwise = case lst of
      []           -> error "insufficient bytes"
      first : rest -> first : getn rest (n - 1)

restn :: [Int] -> Int -> [Int]  -- remove first n bytes from the list
restn lst n
  | n <= 0    = lst
  | otherwise = case lst of
      []          -> error "unable to skip over n bytes"
      _ : rest    -> restn rest (n - 1)

-- Convert a 64-bit number to a list of bytes and get from a list of bytes
n64bytes :: Int64 -> [Int]
n64bytes n = reverse $ makeRevBytes n 8
  where
    makeRevBytes :: Int64 -> Int -> [Int]
    makeRevBytes x index
      | index <= 0 = []
      | otherwise  = fromIntegral (x `mod` 256) : makeRevBytes (x `div` 256) (index - 1)

bytes64 :: [Int] -> Int64
bytes64 lst = compute $ reverse $ getn lst 8
  where
    compute :: [Int] -> Int64
    compute []          = 0
    compute (first:rest) = do
      if first < 0 || first >= 256
        then error "Byte value out of range"
        else fromIntegral first + 256 * compute rest

{-
  4. assert bytes64 (n64bytes n) = n for any n < 2^63
  5. assert n64bytes (bytes64 l) = l for any list of int<256 of length = 8
-}
checkInvariant45 :: IO ()
checkInvariant45 = do
  let maxInt = 2147483646 :: Int64
  n <- randomRIO (0, maxInt)
  
  let makeList 0 = []
      makeList l = randomRIO (0, 255) >>= \r -> (r :) <$> makeList (l - 1)
  
  let makeFirstLessThan128 [] = error "illegal list does not have first"
      makeFirstLessThan128 (first:rest) = 
        (if first >= 128 then first - 128 else first) : rest
  
  let listToString [] = ""
      listToString (first:rest) = show first ++ "." ++ listToString rest
  
  randomList <- makeList 8 >>= return . makeFirstLessThan128
  
  putStr "random int is "
  putStrLn $ show n
  putStr "random list is "
  putStrLn $ listToString randomList
  putStr "random list is now "
  putStrLn $ listToString (n64bytes (bytes64 randomList))
  
  when (bytes64 (n64bytes n) /= n) $
    error "Invariant 4 violated: bytes64 (n64bytes n) != n"
  
  when (n64bytes (bytes64 randomList) /= randomList) $
    error "Invariant 5 violated: n64bytes (bytes64 randomList) != randomList"

-- Make a list of n zeros
makeZeros :: Int64 -> [Int]
makeZeros n
  | n == 0    = []
  | otherwise = 0 : makeZeros (n - 1)

-- Create a block marking an empty set of nb blocks or bytes
makeEmptyBytes :: Device -> Int64 -> [Int]
makeEmptyBytes device nb = n64bytes nb ++ makeZeros (bs device - 8)

makeEmptyBlock :: Device -> Int64 -> [Int]
makeEmptyBlock device nb = makeEmptyBytes device (nb * bs device)

blocksForBytes :: Device -> Int64 -> Int64
blocksForBytes device n = (n + bs device - 1) `div` bs device

-- Clear the device and create an empty set of all blocks
format :: Device -> IO ()
format device = do
  when (bs device <= 9) $ error "Block size must be > 9"
  let zeros = makeZeros (bs device)
  let writeAll n
        | n >= nb device = return ()
        | otherwise = do
            w device n zeros
            writeAll (n + 1)
  
  writeAll 1
  w device 0 (makeEmptyBlock device (nb device))

-- Find an unused block with at least size bytes
findEmpty :: Device -> Int64 -> IO (Int64, Int64)
findEmpty device size = do  -- size includes 8+namelen+1 bytes of header
  let blocks = blocksForBytes device size
  let helper bn
        | bn >= nb device = return (-1, 0)  -- not found
        | otherwise = do
            let block = r device bn
            let fsize = bytes64 block           -- size in bytes
            let nb = blocksForBytes device fsize  -- size in blocks
            let name = restn block 8
            if nb >= blocks && getn name 1 == [0] then do  -- empty block
              when (nb > blocks) $ do             -- some free space
                let numEmpty = nb - blocks
                let newEmpty = makeEmptyBlock device numEmpty
                let newBn = bn + blocks
                w device newBn newEmpty
              return (bn, nb)
            else                            -- go to next block
              helper (bn + nb)
  helper 0

-- Used in the invariants checking
type FileCreated = (String, [Int])
type FileContent = (String, [Int])

newIORef :: a -> IO (IORef a)
newIORef = undefined  -- This would be implemented with IORef in real code

readIORef :: IORef a -> IO a
readIORef = undefined  -- This would be implemented with IORef in real code

writeIORef :: IORef a -> a -> IO ()
writeIORef = undefined  -- This would be implemented with IORef in real code

modifyIORef :: IORef a -> (a -> a) -> IO ()
modifyIORef = undefined  -- This would be implemented with IORef in real code

readErrors :: IORef Int
readErrors = undefined  -- This would be initialized to 0

writeErrors :: IORef Int
writeErrors = undefined  -- This would be initialized to 0

filesCreated :: IORef [FileCreated]
filesCreated = undefined  -- This would be initialized to []

removeFileFromCreated :: String -> IO ()
removeFileFromCreated name = modifyIORef filesCreated removeFile
  where
    removeFile [] = []  -- fail silently if the file doesn't exist
    removeFile ((fname, fcontent):rest)
      | fname == name = rest
      | otherwise     = (fname, fcontent) : removeFile rest

compareByteLists :: Maybe Int -> [Int] -> [Int] -> IO Bool
compareByteLists n c1 c2 = case (c1, c2, n) of
  ([], [], _) -> return True
  (_ : _, [], Nothing) -> return False
  (_ : _, [], Just _) -> putStrLn "c1 is longer" >> return False
  ([], _ : _, Nothing) -> return False
  ([], _ : _, Just _) -> putStrLn "c2 is longer" >> return False
  (h1 : r1, h2 : r2, Nothing) ->
    if h1 == h2 
    then compareByteLists Nothing r1 r2
    else return False
  (h1 : r1, h2 : r2, Just elt) ->
    if h1 == h2 
    then compareByteLists (Just (elt + 1)) r1 r2
    else do
      putStr $ show elt ++ ": "
      putStr $ show h1 ++ " != "
      putStr $ show h2 ++ "\n"
      return False

internalGetHeader :: Device -> Int64 -> IO (Int64, Int64, [Int], [Int], [Int])
internalGetHeader device bn = do
  let block = r device bn
  let fsize = bytes64 block           -- size in bytes
  let nb = blocksForBytes device fsize  -- size in blocks
  let fnameplus = restn block 8
  let separateName [] = ([], [])
      separateName (0:rest) = ([0], rest)
      separateName (c:rest) = 
        let (nameEnd, list) = separateName rest
        in (c : nameEnd, list)
  let (fname, initialData) = separateName fnameplus
  checkInvariant2 (bs device) fname
  return (fsize, nb, fname, initialData, block)

blocksRead :: IORef [Int64]
blocksRead = undefined  -- This would be initialized to []

-- Read or delete are almost the same, so do both in the same function
internalReadOrDelete :: Bool -> Device -> String -> IO (Maybe [Int])
internalReadOrDelete doDelete device name = do
  let nameToList pos
        | pos == length name = [0]
        | otherwise = ord (name !! pos) : nameToList (pos + 1)
  
  let lname = nameToList 0
  
  let clearFile bn nb zeroBlock
        | nb <= 0 = return ()
        | otherwise = do
            w device bn zeroBlock
            clearFile (bn + 1) (nb - 1) zeroBlock
  
  let deleteFile bn nb prevBn prevNb = do
      removeFileFromCreated name
      let getNext bn'
            | bn' >= nb device = return 0
            | otherwise = do
                (_, nb'', fname, _, _) <- internalGetHeader device bn'
                if length fname == 1
                  then do
                    w device bn' (makeZeros (bs device))
                    return nb''
                  else return 0
      nextNb <- getNext (bn + nb)
      let sizeFromBn = (nb + nextNb) * bs device
      let maxBytes = sizeFromBn + prevNb * bs device
      clearFile bn nb (makeZeros (bs device))
      if prevBn == -1
        then w device bn (makeEmptyBytes device sizeFromBn)
        else w device prevBn (makeEmptyBytes device maxBytes)
      return ()
  
  let readAll blockNum remainingSize
        | remainingSize <= 0 = return []
        | otherwise = do
            let block = r device blockNum
            if remainingSize > bs device
              then do
                rest <- readAll (blockNum + 1) (remainingSize - bs device)
                return $ block ++ rest
              else return $ getn block (fromIntegral remainingSize)
  
  let findFile bn prevBn prevNb
        | bn >= nb device = return Nothing          -- not found
        | otherwise = do
            (fsize, nb', fname, initialData, block) <- internalGetHeader device bn
            let hsize = fromIntegral (8 + length fname)
            let dsize = fsize - hsize
            let nextBn = bn + 1
            equal <- compareByteLists Nothing lname fname
            if equal then do      -- found
              result <- if fsize <= bs device
                         then return $ getn initialData (fromIntegral dsize)
                         else do
                           rest <- readAll nextBn (fsize - bs device)
                           return $ initialData ++ rest
              when doDelete $ deleteFile bn nb' prevBn prevNb
              return $ Just result
            else do                               -- not found
              if length fname == 1
                then findFile (bn + nb') bn nb'  -- empty, possible merge
                else findFile (bn + nb') (-1) (-1)
  
  findFile 0 (-1) (-1)

checkInvariant3 :: Device -> IO ()
checkInvariant3 dev = do
  readErrs <- readIORef readErrors
  writeErrs <- readIORef writeErrors
  when (readErrs == 0 && writeErrs == 0) $ do
    created <- readIORef filesCreated
    let verifyFiles [] = return True
        verifyFiles ((name, content):rest) = do
          result <- internalReadOrDelete False dev name
          case result of
            Nothing -> do
              putStrLn (name ++ " not found")
              return False
            Just c -> do
              same <- compareByteLists (Just 0) c content
              if same
                then verifyFiles rest
                else do
                  putStrLn (name ++ " not same")
                  putStr $ show (length c)
                  putStr " =? "
                  putStrLn $ show (length content)
                  return False
    
    verified <- verifyFiles created
    when (not verified) $ error "Invariant 3 violated"

readFile :: Device -> String -> IO (Maybe [Int])
readFile device name = do
  checkInvariant3 device
  internalReadOrDelete False device name

deleteFile :: Device -> String -> IO (Maybe [Int])
deleteFile device name = do
  checkInvariant3 device
  internalReadOrDelete True device name

-- Create a new file with the given data
newFile :: Device -> String -> [Int] -> IO ()
newFile device name data' = do
  checkInvariant3 device
  fileExists <- readFile device name
  nameLength <- return $ fromIntegral (length name + 9)
  
  case fileExists of
    Just _ -> error ("file " ++ name ++ " already exists")
    Nothing
      | nameLength >= bs device -> error "new_file name too long"
      | otherwise -> do
          let nameToList pos
                | pos == length name = [0]
                | otherwise = ord (name !! pos) : nameToList (pos + 1)
          
          let lname = nameToList 0
          
          let writeData bn ddata dlen
                | dlen <= bs device = 
                    w device bn (ddata ++ makeZeros (bs device - dlen))
                | otherwise = do
                    let first = getn ddata (fromIntegral (bs device))
                    let rest = restn ddata (fromIntegral (bs device))
                    w device bn first
                    writeData (bn + 1) rest (dlen - bs device)
          
          let size = fromIntegral (8 + length lname + length data')
          let allData = n64bytes size ++ lname ++ data'
          (bn, nb) <- findEmpty device size
          when (bn < 0) $ error "unable to create file"
          
          modifyIORef filesCreated ((name, data') :)
          writeData bn allData size

listFiles :: Device -> IO [(String, Int64, Int64)]
listFiles device = do
  checkInvariant3 device
  
  let listToName name =
        let intToString i = [chr i]
            substrings = map intToString name
        in concat substrings
  
  let helper bn
        | bn >= nb device = return []          -- no more files
        | otherwise = do
            (fsize, nb', fname, initialData, block) <- internalGetHeader device bn
            let name = listToName (getn fname (length fname - 1))
            let hsize = fromIntegral (8 + length fname)
            let dsize = fsize - hsize
            others <- helper (bn + nb')
            if length fname > 1
              then return $ (name, bn, dsize) : others
              else return others
  
  helper 0

-- Test stuff
blocks :: Array.Array Int [Int]
blocks = Array.array (0, 499) [(i, []) | i <- [0..499]]

readBlock :: Int64 -> Int64 -> [Int]
readBlock bs n = do
  let data' = blocks Array.! fromIntegral n
  checkInvariant1 bs data'
  data'

writeBlock :: Int64 -> Int64 -> [Int] -> IO ()
writeBlock bs n b = do
  checkInvariant1 bs b
  -- Array.// would update and return a new array, but we're mimicking mutable behavior
  -- In a real implementation, this would use a mutable array or IOArray

makeData :: Int -> [Int]
makeData 0 = []
makeData n = (n `mod` 256) : makeData (n - 1)

testDevice :: Device
testDevice = 
  let bs' = 512
  in Device {
    name = "test",
    bs = bs',
    nb = 100,
    r = readBlock bs',
    w = writeBlock bs'
  }

data' :: [Int]
data' = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

-- Two blocks' worth of data
ld :: [Int]
ld = concat $ replicate 70 data'

makeFiles :: Device -> [(String, Int)] -> IO ()
makeFiles _ [] = return ()
makeFiles device ((fname, fsize):rest) = do
  putStrLn ("making file " ++ fname)
  newFile device fname (makeData fsize)
  makeFiles device rest

sampleFiles1 :: [(String, Int)]
sampleFiles1 = [
  ("a", 10), ("b", 600), ("c", 512), ("d", 500), ("e", 501),
  ("f", 502), ("g", 503), ("h", 504), ("i", 505),
  ("j", 10000), ("k", 1), ("l", 0)]

-- Print the non-zero part of non-zero blocks
printBlocks :: Device -> Int64 -> IO ()
printBlocks device max' = do
  let blen = fromIntegral (Array.bounds blocks) -- this approximates Array.length
  let dlen = if nb device < blen then nb device else blen
  let actualMax = if max' <= 0 || max' > dlen then dlen else max'
  
  let isZeros [] = True
      isZeros (0:rest) = isZeros rest
      isZeros _ = False
  
  let printBlock lst min'
        | min' <= 0 && isZeros lst = return ()
        | otherwise = case lst of
            [] -> if min' <= 0 
                  then error "no bytes in print_block" 
                  else printBlock (makeZeros min') min'
            first:rest -> do
              putStr $ show first ++ " "
              printBlock rest (min' - 1)
  
  let printAll n
        | n < actualMax = do
            let a = readBlock (bs device) n
            unless (isZeros a) $ do
              putStr $ show (fromIntegral n) ++ ": "
              printBlock a 8
              putStrLn ""
            printAll (n + 1)
        | otherwise = return ()
  
  printAll 0

p :: IO ()
p = printBlocks testDevice 0

-- Main function to run tests
main :: IO ()
main = do
  checkInvariant45
  format testDevice
  makeFiles testDevice sampleFiles1
  p