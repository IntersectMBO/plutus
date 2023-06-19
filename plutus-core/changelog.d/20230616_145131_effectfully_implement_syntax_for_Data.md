### Changed

- Updated the parser and the pretty-printers to the new syntax of `Data` in [#5391](https://github.com/input-output-hk/plutus/pull/5391) according to [this](https://github.com/input-output-hk/plutus/issues/4751#issuecomment-1538377273), for example:

```
Constr 1
  [ Map [(B #616263646566, Constr 2 [B #, I 0])]
  , List
      [ List
          [ List [List [I 123456]]
          , B #666666666666666666666666666666666666666666666666666666666666666666666666666666666666 ] ]
  , I 42 ]
```
