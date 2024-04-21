#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck-2.14.2

import Data.Monoid
import Data.Foldable
import Test.QuickCheck

-- Define Basis3 with three elements
data Basis3 = A | B | C deriving (Eq, Show)

toEnumBasis3 :: Int -> Basis3
toEnumBasis3 0 = A
toEnumBasis3 1 = B
toEnumBasis3 _ = C

fromEnumBasis3 :: Basis3 -> Int
fromEnumBasis3 A = 0
fromEnumBasis3 B = 1
fromEnumBasis3 C = 2

toEnumMax3 :: Int -> Max3 Basis3
toEnumMax3 0 = (Max3 A)
toEnumMax3 1 = (Max3 B)
toEnumMax3 _ = (Max3 C)

fromEnumMax3 :: Max3 Basis3 -> Int
fromEnumMax3 (Max3 A) = 0
fromEnumMax3 (Max3 B) = 1
fromEnumMax3 (Max3 C) = 2

-- Make Basis3 an instance of Arbitrary for QuickCheck testing
instance Arbitrary Basis3 where
    arbitrary = elements [A, B, C]

-- Define a new Monoid to replace Max3 for three elements
data Max3 a = Max3 {fromMax3 :: a} deriving (Eq, Show)

instance Semigroup (Max3 Basis3) where
    x <> y = toEnumMax3 $ max (fromEnumMax3 x) (fromEnumMax3 y)

instance Monoid (Max3 Basis3) where
    mempty = toEnumMax3 0

-- Make Max3 an instance of Arbitrary
instance Arbitrary (Max3 Basis3) where
    arbitrary = elements [Max3 A, Max3 B, Max3 C]

class Free m where
    canonicalInj :: b -> m b

-- Monoid properties
-- Left Identity
prop_leftIdentity :: (Eq m, Monoid m, Show m) => m -> Property
prop_leftIdentity x = mempty <> x === x

-- Right Identity
prop_rightIdentity :: (Eq m, Monoid m, Show m) => m -> Property
prop_rightIdentity x = x <> mempty === x

-- Associativity
prop_associativity :: (Eq m, Monoid m, Show m) => m -> m -> m -> Property
prop_associativity x y z = (x <> y) <> z === x <> (y <> z)


-- Homomorphism Properties
-- Identity Preservation Property
prop_identityPreservation :: (Monoid a, Monoid b, Eq b, Show b) => (a -> b) -> Property
prop_identityPreservation homomorphism =
  homomorphism mempty === mempty

-- Operation Preservation Property
prop_operationPreservation :: (Monoid a, Monoid b, Eq b, Show b) => (a -> b) -> a -> a -> Property
prop_operationPreservation homomorphism x y =
  homomorphism (x <> y) === (homomorphism x <> homomorphism y)

-- Universal Property (Commuting triangle)
prop_universal_property_commuting :: (Eq a, Show a, Free f) => (Basis3 -> a) -> (f Basis3 -> a) -> Basis3 -> Property
prop_universal_property_commuting testMap homomorphism = commutesOnInput
  where commutesOnInput input = testMap input === (homomorphism . canonicalInj) input

prop_equal_on_generators :: (Eq a, Show a, Free f) => (f Basis3 -> a) -> (f Basis3 -> a) -> Basis3 -> Property
prop_equal_on_generators homomorphism1 homomorphism2 = commutesOnInput
  where commutesOnInput input = (homomorphism1 . canonicalInj) input === (homomorphism2 . canonicalInj) input

prop_unique_universal_morphism :: (Eq a, Show a) => (t -> a) -> (t -> a) -> t -> Property
prop_unique_universal_morphism morphism1 morphism2 input = (morphism1 input === morphism2 input)


----------------------------
-- (Testing for Freeness) --
----------------------------
------ MaybeList Basis3 --------
----------------------------
newtype MaybeList a = MaybeList {fromMaybeList :: Maybe [a]} deriving (Show, Eq)
instance Free MaybeList where
    canonicalInj = MaybeList . Just . (:[])

instance Arbitrary a => Arbitrary (MaybeList a) where
    arbitrary = MaybeList <$> arbitrary

instance Semigroup (MaybeList a) where
    (MaybeList x) <> (MaybeList y) = MaybeList (x <> y)

instance Monoid (MaybeList a) where
    mempty = MaybeList mempty

maybeBasis3List_IsNotFree_Proof1 :: IO ()
maybeBasis3List_IsNotFree_Proof1 = do
    putStrLn "Testing MaybeList Basis3 for monoid laws:"
    quickCheck (prop_leftIdentity :: MaybeList Basis3 -> Property)
    quickCheck (prop_rightIdentity :: MaybeList Basis3 -> Property)
    quickCheck (prop_associativity :: MaybeList Basis3 -> MaybeList Basis3 -> MaybeList Basis3 -> Property)
    putStr "\n"

    putStrLn "Testing Max3 for monoid laws:"
    quickCheck (prop_leftIdentity :: Max3 Basis3 -> Property)
    quickCheck (prop_rightIdentity :: Max3 Basis3 -> Property)
    quickCheck (prop_associativity :: Max3 Basis3 -> Max3 Basis3 -> Max3 Basis3 -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties MaybeList Basis3 To Max3:"
    quickCheck (prop_identityPreservation maybeBasis3ListToMax31)
    quickCheck (prop_identityPreservation maybeBasis3ListToMax32)
    quickCheck (prop_operationPreservation maybeBasis3ListToMax31)
    quickCheck (prop_operationPreservation maybeBasis3ListToMax32)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBasis3ListToMax31"
    quickCheck (prop_universal_property_commuting g maybeBasis3ListToMax31)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBasis3ListToMax32"
    quickCheck (prop_universal_property_commuting g maybeBasis3ListToMax32)
    putStr "\n"

    putStrLn "Testing if homomorphism is non-unique:"
    quickCheck (prop_equal_on_generators maybeBasis3ListToMax31 maybeBasis3ListToMax32)
    quickCheck (prop_unique_universal_morphism maybeBasis3ListToMax31 maybeBasis3ListToMax32 :: MaybeList Basis3 -> Property)
    putStr "\n"
    putStr "\n"
  where -- g is a counter example to any g between sets Basis -> UnderlyingSetOf SomeMonoid having a unique homomorphism (where SomeMonoid = Max3)
        g :: Basis3 -> Max3 Basis3
        g A = Max3 C
        g B = Max3 C
        g C = Max3 C
        
        maybeBasis3ListToMax31 :: MaybeList Basis3 -> Max3 Basis3
        maybeBasis3ListToMax31 (MaybeList Nothing  ) = Max3 A
        maybeBasis3ListToMax31 (MaybeList (Just [])) = Max3 A
        maybeBasis3ListToMax31 (MaybeList (Just xs)) = Max3 C
        
        maybeBasis3ListToMax32 :: MaybeList Basis3 -> Max3 Basis3
        maybeBasis3ListToMax32 (MaybeList Nothing  ) = Max3 A
        maybeBasis3ListToMax32 (MaybeList (Just [])) = Max3 C
        maybeBasis3ListToMax32 (MaybeList (Just xs)) = Max3 C

maybeBasis3List_IsNotFree_Proof2 :: IO ()
maybeBasis3List_IsNotFree_Proof2 = do
    putStrLn "Testing MaybeList Basis3 for monoid laws:"
    quickCheck (prop_leftIdentity :: MaybeList Basis3 -> Property)
    quickCheck (prop_rightIdentity :: MaybeList Basis3 -> Property)
    quickCheck (prop_associativity :: MaybeList Basis3 -> MaybeList Basis3 -> MaybeList Basis3 -> Property)
    putStr "\n"
    
    putStrLn "Testing MaybeList Basis3 for monoid laws:"
    quickCheck (prop_leftIdentity :: MaybeList Basis3 -> Property)
    quickCheck (prop_rightIdentity :: MaybeList Basis3 -> Property)
    quickCheck (prop_associativity :: MaybeList Basis3 -> MaybeList Basis3 -> MaybeList Basis3 -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties MaybeList Basis3 To MaybeList Basis3:"
    quickCheck (prop_identityPreservation maybeBasis3ListToMaybeBasis3List1)
    quickCheck (prop_identityPreservation maybeBasis3ListToMaybeBasis3List2)
    quickCheck (prop_operationPreservation maybeBasis3ListToMaybeBasis3List1)
    quickCheck (prop_operationPreservation maybeBasis3ListToMaybeBasis3List2)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for testMap1 and maybeBasis3ListToMaybeBasis3List1"
    quickCheck (prop_universal_property_commuting testMap1 maybeBasis3ListToMaybeBasis3List1)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for testMap1 and maybeBasis3ListToMaybeBasis3List2"
    quickCheck (prop_universal_property_commuting testMap1 maybeBasis3ListToMaybeBasis3List2)
    putStr "\n"

    putStrLn "Testing if homomorphism is non-unique:"
    quickCheck (prop_equal_on_generators maybeBasis3ListToMaybeBasis3List1 maybeBasis3ListToMaybeBasis3List2)
    quickCheck (prop_unique_universal_morphism maybeBasis3ListToMaybeBasis3List1 maybeBasis3ListToMaybeBasis3List2 :: MaybeList Basis3 -> Property)
    putStr "\n"
    putStr "\n"
  where testMap1 :: Basis3 -> MaybeList Basis3
        testMap1 A = MaybeList (Just [A])
        testMap1 B  = MaybeList (Just [B])
        testMap1 C  = MaybeList (Just [C])
        
        maybeBasis3ListToMaybeBasis3List1 :: MaybeList Basis3 -> MaybeList Basis3
        maybeBasis3ListToMaybeBasis3List1 (MaybeList Nothing  ) = MaybeList (Nothing)
        maybeBasis3ListToMaybeBasis3List1 (MaybeList (Just [])) = MaybeList (Nothing)
        maybeBasis3ListToMaybeBasis3List1 (MaybeList (Just xs)) = MaybeList (Just xs)

        maybeBasis3ListToMaybeBasis3List2 :: MaybeList Basis3 -> MaybeList Basis3
        maybeBasis3ListToMaybeBasis3List2 (MaybeList Nothing  ) = MaybeList (Nothing)
        maybeBasis3ListToMaybeBasis3List2 (MaybeList (Just [])) = MaybeList (Just [])
        maybeBasis3ListToMaybeBasis3List2 (MaybeList (Just xs)) = MaybeList (Just xs)


----------------------------
-- (Testing for Freeness) --
----------------------------
--------- [Basis3] -----------
----------------------------

instance Free [] where
    canonicalInj = (:[])

type UnderLyingSetOfMax3 = Basis3
basis3List_IsFree_For_Max3 :: IO ()
basis3List_IsFree_For_Max3 = do
    putStrLn "Testing [Basis3] for monoid laws:"
    quickCheck (prop_leftIdentity :: [Basis3] -> Property)
    quickCheck (prop_rightIdentity :: [Basis3] -> Property)
    quickCheck (prop_associativity :: [Basis3] -> [Basis3] -> [Basis3] -> Property)
    putStr "\n"

    putStrLn "Testing Max3 for monoid laws:"
    quickCheck (prop_leftIdentity :: Max3 Basis3 -> Property)
    quickCheck (prop_rightIdentity :: Max3 Basis3 -> Property)
    quickCheck (prop_associativity :: Max3 Basis3 -> Max3 Basis3 -> Max3 Basis3 -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties [Basis3] To Max3:"
    sequence $ [quickCheck (prop_identityPreservation basis3ListToMax3) | triMap <- allBasis3Maps, let testMap = Max3 . triMap, let basis3ListToMax3 = foldMap Max3 . map triMap]
    sequence $ [quickCheck (prop_operationPreservation basis3ListToMax3) | triMap <- allBasis3Maps, let testMap = Max3 . triMap, let basis3ListToMax3 = foldMap Max3 . map triMap]
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting"
    sequence $ [quickCheck (prop_universal_property_commuting testMap basis3ListToMax3) | triMap <- allBasis3Maps, let testMap = Max3 . triMap, let basis3ListToMax3 = foldMap Max3 . map triMap]
    putStr "\n"
    putStr "\n"
  where allBasis3Maps :: [Basis3 -> UnderLyingSetOfMax3]
        allBasis3Maps = [f x y z | [x,y,z] <- sequence (replicate 3 [A,B,C])]
        
        f x y z = func
          where func A = x
                func B = y
                func C = z

main = do
    maybeBasis3List_IsNotFree_Proof1
    maybeBasis3List_IsNotFree_Proof2
    basis3List_IsFree_For_Max3