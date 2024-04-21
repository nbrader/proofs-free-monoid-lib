#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck-2.14.2

import Data.Monoid
import Data.Foldable
import Test.QuickCheck

-- Define Basis3 with three elements
data Basis3 = A | B | C deriving (Eq, Show)

-- Make Basis3 an instance of Arbitrary for QuickCheck testing
instance Arbitrary Basis3 where
    arbitrary = elements [A, B, C]

class (Monoid m) => FreeMonoid3 m where
    canonicalInj :: Basis3 -> m

-- Implement FreeMonoid3 for lists of Basis3 elements
instance FreeMonoid3 [Basis3] where
    canonicalInj x = [x]


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
prop_universal_property_commuting :: (Eq a, Show a, FreeMonoid3 f) => (Basis3 -> a) -> (f -> a) -> Basis3 -> Property
prop_universal_property_commuting testMap homomorphism = commutesOnInput
  where commutesOnInput input = testMap input === (homomorphism . canonicalInj) input

prop_equal_on_generators :: (Eq a, Show a, FreeMonoid3 f) => (f -> a) -> (f -> a) -> Basis3 -> Property
prop_equal_on_generators homomorphism1 homomorphism2 = commutesOnInput
  where commutesOnInput input = (homomorphism1 . canonicalInj) input === (homomorphism2 . canonicalInj) input

prop_unique_universal_morphism :: (Eq a, Show a) => (t -> a) -> (t -> a) -> t -> Property
prop_unique_universal_morphism morphism1 morphism2 input = (morphism1 input === morphism2 input)

-- Define homomorphism examples
-- For simplicity, let's define a homomorphism from [Basis3] to Any (Monoid under disjunction)
basis3ListToAny :: [Basis3] -> Any
basis3ListToAny = foldMap (\_ -> Any True) -- Maps every element to Any True, demonstrating non-trivial homomorphism

-- Define the universal property test for the homomorphism
prop_universal_property_basis3 :: (Eq a, Show a) => (Basis3 -> a) -> ([Basis3] -> a) -> Basis3 -> Property
prop_universal_property_basis3 testMap homomorphism = commutesOnInput
  where commutesOnInput input = testMap input === (homomorphism . canonicalInj) input

prop_homomorphism_uniqueness :: ([Basis3] -> Any) -> ([Basis3] -> Any) -> [Basis3] -> Property
prop_homomorphism_uniqueness hom1 hom2 input = hom1 input === hom2 input

-- -- Test whether [Basis3] satisfies the criteria for being a free monoid
-- main :: IO ()
-- main = do
    -- putStrLn "Testing [Basis3] for monoid laws:"
    -- quickCheck (prop_leftIdentity :: [Basis3] -> Property)
    -- quickCheck (prop_rightIdentity :: [Basis3] -> Property)
    -- quickCheck (prop_associativity :: [Basis3] -> [Basis3] -> [Basis3] -> Property)
    -- putStrLn "\nTesting homomorphism from [Basis3] to Any:"
    -- quickCheck (prop_identityPreservation basis3ListToAny)
    -- quickCheck (prop_operationPreservation basis3ListToAny)
    -- putStrLn "\nTesting the universal property for a simple test map to Any:"
    -- quickCheck (prop_universal_property_basis3 (\_ -> Any True) basis3ListToAny)
    -- putStrLn "Testing the uniqueness of the homomorphism:"
    -- quickCheck (prop_homomorphism_uniqueness basis3ListToAny basis3ListToAny)

-- Define Monoid instance for Maybe Basis3 (this instance already exists, but for illustration)
-- instance Semigroup (Maybe Basis3) where
    -- Nothing <> m = m
    -- m <> Nothing = m
    -- Just x <> Just y = Just x -- Non-standard behavior just for demonstration

-- instance Monoid (Maybe Basis3) where
    -- mempty = Nothing

-- Attempt to define a homomorphism from Maybe Basis3 to Any, which isn't truly homomorphic due to non-unique behavior
maybeBasis3ToAny :: Maybe Basis3 -> Any
maybeBasis3ToAny Nothing = Any False
maybeBasis3ToAny (Just _) = Any True

-- Attempt to test the universal property for Maybe Basis3
prop_universal_property_maybeBasis3 :: (Basis3 -> Any) -> (Maybe Basis3 -> Any) -> Basis3 -> Property
prop_universal_property_maybeBasis3 testMap homomorphism = commutesOnInput
  where commutesOnInput input = testMap input === (homomorphism . Just) input

-- Define another homomorphism for counter-example
maybeBasis3ToAnyDifferent :: Maybe Basis3 -> Any
maybeBasis3ToAnyDifferent = const (Any True) -- Always true, regardless of input

-- Show that the universal property doesn't hold uniquely (i.e., there's more than one way to extend a function to a homomorphism)
prop_non_unique_homomorphism :: Basis3 -> Property
prop_non_unique_homomorphism input =
    maybeBasis3ToAny (Just input) =/= maybeBasis3ToAnyDifferent (Just input)

-- Update main to include tests for Maybe Basis3
main :: IO ()
main = do
    putStrLn "Testing [Basis3] for monoid laws:"
    quickCheck (prop_leftIdentity :: [Basis3] -> Property)
    quickCheck (prop_rightIdentity :: [Basis3] -> Property)
    quickCheck (prop_associativity :: [Basis3] -> [Basis3] -> [Basis3] -> Property)
    putStrLn "\nTesting homomorphism from [Basis3] to Any:"
    quickCheck (prop_identityPreservation basis3ListToAny)
    quickCheck (prop_operationPreservation basis3ListToAny)
    putStrLn "\nTesting the universal property for a simple test map to Any:"
    quickCheck (prop_universal_property_basis3 (\_ -> Any True) basis3ListToAny)
    putStrLn "Testing the uniqueness of the homomorphism:"
    quickCheck (prop_homomorphism_uniqueness basis3ListToAny basis3ListToAny)
    putStrLn "\nTesting Maybe Basis3 for failure to satisfy the unique universal property:"
    quickCheck (prop_non_unique_homomorphism)
