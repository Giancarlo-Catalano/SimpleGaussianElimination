import Data.Char
import Data.List
import Data.Function 
import Data.Maybe


type RowIndex = Int
type ColumnIndex = Int



data Matrix = Matrix [[Int]] 

getDimensions :: Matrix -> (Int, Int)
getDimensions (Matrix rows) = (length rows, length $ head rows)

data MatrixOperation = 
      Rearrangement [RowIndex]
    | RowDivision RowIndex Int
    | RowDivisions [MatrixOperation]
    | RowMultiplication RowIndex Int  --only used internally
    | RowSum RowIndex MatrixOperation MatrixOperation  --used internally
    | RowNullfications [MatrixOperation]  
    | NoOperation 


findCommonDivisor :: [Int] -> Maybe Int
findCommonDivisor l = let divisors n = let n' = abs n in [a | a<-[1..n'], n' `mod` a == 0]
                          nonZeros = filter (/=0) l
                          commonDivisors = if (null nonZeros) then []
                                                              else foldl1 intersect $ map divisors nonZeros
                          firstNonZero = head nonZeros
                          firstNonZeroIsNegative = firstNonZero < 0
                          bestPositiveDivisor = maximum commonDivisors
                          bestDivisor = if firstNonZeroIsNegative then negate bestPositiveDivisor else bestPositiveDivisor
                      in  case commonDivisors of [] -> Nothing
                                                 [1] -> Nothing
                                                 other -> Just bestDivisor


divideRows :: Matrix -> (Matrix, MatrixOperation)
divideRows (Matrix rows) =   let rowDivision acc (ri, r) = case findCommonDivisor r of Nothing -> acc
                                                                                       Just d -> acc++[RowDivision ri d]
                                 changes = foldl rowDivision [] $ zip [0..] rows
                                 applyChange (Matrix acc) (RowDivision ri d) = let beforeI = take ri acc
                                                                                   afterI = drop (ri+1) acc
                                                                                   newRi = map (flip div d) (acc!!ri)
                                                                               in  Matrix $ beforeI++[newRi]++afterI
                                 finalMatrix = foldl applyChange (Matrix rows) changes
                             in  if null changes then (Matrix rows, NoOperation)
                                                 else (finalMatrix, RowDivisions changes)



findPermutation old srt = let getPositionAndRecord acc e = let Just goodOne = find (\g->notElem g acc) $ elemIndices e srt
                                                           in  goodOne:acc
                          in  reverse $ foldl getPositionAndRecord [] old

rearrangeMatrixRows :: Matrix -> (Matrix, MatrixOperation)
rearrangeMatrixRows (Matrix rows) = let compareRows (0:xs) (0:ys) = compareRows xs ys
                                        compareRows (0:xs) y = GT
                                        compareRows x (0:ys) = LT
                                        compareRows (1:xs) (1:ys) = EQ
                                        compareRows x (1:ys) = GT
                                        compareRows (1:xs) y = LT
                                        compareRows x y = EQ
                                        sortedRows = sortBy compareRows rows
                                        perm = findPermutation rows sortedRows
                                    in  if rows == sortedRows then (Matrix rows, NoOperation) 
                                                              else (Matrix sortedRows, Rearrangement perm)

                                        


findColumnToNullify :: Matrix -> Maybe (RowIndex, ColumnIndex) 
findColumnToNullify (Matrix []) = Nothing
findColumnToNullify m = let findAntiCoords (Matrix []) = Nothing
                            findAntiCoords (Matrix ([]:rs)) = Nothing
                            findAntiCoords (Matrix rows) =  let removeRow = tail
                                                                removeColumn = map tail
                                                                firstColumn = map head rows
                                                                restIsZeros c = all (==0) $ tail c
                                                                firstColumnIsDone = restIsZeros firstColumn
                                                                newRows = if (head firstColumn) /= 0
                                                                            then removeRow $ removeColumn rows
                                                                            else removeColumn rows
                                                                innerMatrix = Matrix newRows
                                                            in  if firstColumnIsDone 
                                                                    then findAntiCoords innerMatrix
                                                                    else Just $ getDimensions (Matrix rows)
                                    in  do
                                            (antiRow, antiColumn) <- findAntiCoords m
                                            let (rowCount, columnCount) = getDimensions m
                                            return (rowCount-antiRow, columnCount-antiColumn)


applyRowSum :: Matrix -> MatrixOperation -> Matrix
applyRowSum (Matrix rows) (RowSum ri (RowMultiplication rai coeffA) (RowMultiplication rbi coeffB)) =   let beforeR = take ri rows
                                                                                                            afterR = drop (ri+1) rows
                                                                                                            rb = rows!!rbi
                                                                                                            ra = rows!!rai
                                                                                                            newR = zipWith (+) (map (* coeffA) ra) (map (* coeffB) rb)
                                                                                                        in  Matrix $ beforeR ++ [newR] ++ afterR

getCoeffsToNullify :: Int -> Int -> (Int, Int)   --if the column a starts with A and b starts with B, what are X, Y s.y A*X+B*Y = 0 ?
getCoeffsToNullify 0 b = (1, 0)
getCoeffsToNullify a 0 = (0, 1)
getCoeffsToNullify a b
                    | (mod a b) == 0 = (-1, div a b)
                    | (mod b a) == 0 = (negate (div b a), 1)
                    | otherwise = (-b, a) 


nullifyColumns :: Matrix -> (Matrix, MatrixOperation)
nullifyColumns m@(Matrix rows) = let getNullifications (rl, cl) =  let fullColumn = map (!!cl) rows
                                                                       getNullificationOperation rai rbi = let (raHead, rbHead) = (fullColumn!!rai, fullColumn!!rbi)
                                                                                                               (coeffA, coeffB) = getCoeffsToNullify raHead rbHead
                                                                                                           in  RowSum rbi (RowMultiplication rbi coeffB) (RowMultiplication rai coeffA)
                                                                       rowIndexesToBeNullified = [ri | (ri, rhead) <- drop (rl+1) $ zip [0..] fullColumn, rhead/=0]
                                                                   in  map (getNullificationOperation rl) rowIndexesToBeNullified 
                                 in  case findColumnToNullify m of Nothing -> (m, NoOperation)
                                                                   Just leadInfo -> let nullifications = getNullifications leadInfo
                                                                                    in  (foldl applyRowSum m nullifications, RowNullfications nullifications)
                                         

repeatReduce :: Matrix -> [(Matrix, [MatrixOperation])]
repeatReduce m = let unliftOp op (m, oldOp) = let (m2, newOp) = op m
                                              in  (m2, oldOp++[newOp])
                     reduceMatrix (m,_) = let (m1, divisions) = divideRows m
                                              (m2, nullifs) = nullifyColumns m1
                                              (m3, rearrs) = rearrangeMatrixRows m2
                                              (m4, moreDivs) = divideRows m3
                                          in  (m4, divisions:nullifs:rearrs:moreDivs:[])
                     canBeReduced (m, _) = (findColumnToNullify m) /= Nothing
                     iterations = iterate reduceMatrix (m, [])
                     steps = takeWhile canBeReduced iterations
                     finalResult = reduceMatrix $ last steps
                 in  steps++[finalResult]



showReductionSteps steps = let showOps ops = unlines $ map show ops
                               showStep (m, ops) = (replicate 20 '-')++"\n"++(showOps ops)++(show m)
                           in  concatMap showStep steps



showYourProcess = putStrLn . showReductionSteps . repeatReduce 


--TODO implement backtracking


tm = Matrix [[1, 3, 0, 1, 0],[1, 4, 2, 0, 0], [0, -2, -2, -1, 0], [2, -4, 1, 1, 0], [1, -2, -1, 1, 0]]

tn = Matrix [[1, 0, 3, -2, 0], [1, 2, -4, 3, 0], [3, 2, 2, -1, 0]]


ta = Matrix [[1,3,0,1,0],[0,1,2,-1,0],[0,0,9,-5,0],[0,0,0,6,0],[0,0,0,-17,0]]



{--matrixToLinearSum :: Matrix -> [[Int]]
matrixToLinearSum (Matrix rows) = let isUsableRow = all (/= 0)
                                      usableRows = filter isUsableRow rows
                                  in  undefined
--}

{--

HOW TO USE:

ghci gaussElimination.hs

showYourProcess (Matrix [[...],[...]])

for example:
    showYourProcess (Matrix [[1, 0, 3, -2, 0], [1, 2, -4, 3, 0], [3, 2, 2, -1, 0]])

--}



showAsSubscriptNumber :: (Show a)=> a -> String
showAsSubscriptNumber a = let initialString = show a
                              digitToSub c = chr $ 8272 + (ord c)  --this is nasty
                              convertChar c = if isDigit c then digitToSub c else c
                          in  map convertChar $ initialString


showRow :: RowIndex -> String
showRow ri = "R"++(showAsSubscriptNumber (ri+1))


instance Show MatrixOperation where

    show NoOperation = ""
    show (Rearrangement rs) = let oldNewPosPairs = zip [0..] rs
                                  isChange (a, b) = a/=b 
                                  posPairs = filter isChange oldNewPosPairs
                                  swappedPair (a, b) = (b, a)
                                  isLowerGreater (a, b) = a <= b
                                  swaps = [pair | pair<-posPairs, elem (swappedPair pair) posPairs, isLowerGreater pair]
                                  redundantSwaps = swaps++(map swappedPair swaps)
                                  moves = posPairs \\ redundantSwaps
                                  swapSymbol = "⇄"
                                  moveSymbol = "🠒"
                                  showSwap (a, b) = (showRow a)++" "++swapSymbol++" "++(showRow b)
                                  showMove (a, b) = (showRow a)++" "++moveSymbol++" "++(showRow b)
                                  commaSeparated = intercalate ", " $ (map showSwap swaps)++(map showMove moves)
                              in  if ((null swaps) && (null moves)) then ""
                                    else "Rearrangement: "++commaSeparated

    show (RowDivisions rds) = if (null rds) then "" else "Divisions"++(concatMap ("\n\t"++) $ map show rds)

    show (RowDivision ri coeff) = (showRow ri)++" = "++(showRow ri)++"/"++(show coeff)

    show (RowMultiplication ri coeff) = let coeffString = case coeff of 1 -> ""
                                                                        -1 -> "-"
                                                                        other -> (show coeff)++"⋅"
                                        in  coeffString ++ (showRow ri)

    show (RowSum ri rma rmb) = let assignmentString = (showRow ri)++" = "
                                   isCoeffNegative = let (RowMultiplication _ coeff) = rmb
                                                     in  coeff < 0
                                   sumString = if isCoeffNegative then (show rma)++""++(show rmb)
                                                                  else (show rma)++"+"++(show rmb)
                               in  assignmentString ++ sumString
    show (RowNullfications nullifs) = "Nullifications:"++(concatMap ("\n\t"++) $ map show nullifs)




showListOfMatrixOperations ops = unlines $ filter (/="") $ map show ops





instance Show Matrix where
    show (Matrix rows) = let longestLength = maximum $ map (length . show) $ concat rows
                             showWithRightLength a = let shown = show a
                                                         currLength = length shown
                                                         paddingRequired = longestLength - (length shown)
                                                     in  (replicate paddingRequired ' ')++shown
                             showRow r = let (lhs, rhs) = (init r, last r)
                                         in  (intercalate " " $ map showWithRightLength lhs)++"│"++(showWithRightLength rhs)
                         in unlines $ map showRow rows



augmentMatrix :: Matrix -> [Int] -> Matrix
augmentMatrix (Matrix rows) newC = let addLast row e = row++[e]
                                   in  Matrix $ zipWith addLast rows newC



fromStringToMatrix :: String -> Matrix
fromStringToMatrix str = let elems :: [[Int]]
                             elems =  map (map read) $ map words $ lines str
                         in  Matrix elems


main = do
          fileString <- readFile "matrix.txt"
          let initialMatrix = fromStringToMatrix fileString
              resultMatrixOperationsAsString = showReductionSteps $ repeatReduce initialMatrix
              footer = "\n\n\n\n...Program made by GC 2021 at Stirling Uni 🐌"
              result = resultMatrixOperationsAsString++footer
          writeFile "steps.txt" result
          putStrLn "Done simplifying\n"