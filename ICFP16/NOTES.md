
---

To submit to [ICFP 2016](http://conf.researchr.org/home/icfp-2016) ([CFP](http://conf.researchr.org/track/icfp-2016/icfp-2016-papers#Call-for-Papers))

   - submission: https://icfp2016.hotcrp.com/
   - deadline: Wednesday, March 16 2016, 15:00 (UTC)
       + (tentative deadline: prepare it until February 15, 2016)
   - pages: 12 (excluding bibliography)

---

# The Under-Appreciated Put : Implementing Delta-Alignment in BiGUL

Alignment can already be performed within BiGUL using the `align` construct.
This alignment is specific to lists and has a fixed strategy with key-based
matching. However, `align` has more features:
   - list element filtering;
   - concealment of deleted elements from the view.

## Container Element Alignment Using Deltas

### Implementation in BiGUL

Currently, two implementations of alignment with deltas are provided:

   - alignment between lists; and,
   - alignment between any shapely type and lists.

The former is simpler than the latter, since the latter requires a function to
reshape the source and provide the default value for new elements.

#### With list containers.

Alignment as a BiGUL program, receiving the delta as a parameter:
```haskell
pAlign
  :: (MonadError' ErrorInfo m, Eq a, Eq b, Eq (s b), Shapely s, s ~ [])
  => BiGUL m a b              -- ^Inner BiGUL program.
  -> (b -> a)                 -- ^Create function.
  -> (PosMapping (s b, s b))  -- ^View delta.
  -> BiGUL m (s a) (s b)
```
This implementation cannot be used with the BiGUL `create` function since it
is implemented embedding the `pAlign'` function.

Alignment as a BiGUL program, where the delta is part of the source:
```haskell
pAlign'
  :: (MonadError' ErrorInfo m, Eq a, Eq b, Eq (s b), Shapely s, s ~ [])
  => BiGUL m a b -- ^Inner BiGUL program.
  -> (b -> a)    -- ^Create function.
  -> BiGUL m (s a, (PosMapping (s b, s b))) (s b)
```

#### With any shapely type as source and list as view.

```haskell
pAlignG
  :: (MonadError' ErrorInfo m, Eq a, Eq b, Eq (s a), Eq (v b), Eq (v One), Shapely s, Shapely v, v ~ [])
  => BiGUL m a b                                     -- ^Inner BiGUL program.
  -> ((s a) -> (v b) -> (PosMapping (v b)) -> (s a)) -- ^Adaption function.
  -> (PosMapping (s b, s b))                         -- ^View delta.
  -> BiGUL m (s a) (v b)
```

```haskell
pAlignG'
  :: (MonadError' ErrorInfo m, Eq a, Eq b, Eq (s a), Eq (v b), Eq (v One), Shapely s, Shapely v, v ~ [])
  => BiGUL m a b
  -> ((s a) -> (v b) -> (PosMapping (v b)) -> (s a))
  -> PosMapping (v b)
  -> BiGUL m (SourceShape s a, (PosMapping (v b, v b))) (ViewShape v b)
```

## Shape Alignment

   - get horizontal delta - needed for the alignment of distinct containers.
     When the containers are the same, the horizontal delta is "id".

## Other Contributions

   - create - needed in some situations, e.g., the sum combinator.

## Aspects to Tackle

   - future work from the matching lenses paper
   - examples of BiGUL alignment programs (e.g., binary tree <-> list, and
     balanced tree)
   - BiGUL alignment vs matching lenses: with BiGUL it's simpler and more
     flexible
   - BiGUL alignment vs delta-alignment over inductive types: BiGUL is simpler
   - BiGUL interface freeze (i.e., provide a stable API with the features from
     this paper)
