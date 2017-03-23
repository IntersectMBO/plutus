/*

data CKFrame = InLet (Scope TermF)
             | InAppLeft Term
             | InAppRight Term
             | InCon String [Term] [Term]
             | InCase [Term] [Term] [ClauseF (Scope TermF)]
             | InSuccess
             | InBind (Scope TermF)
             | InBuiltin String [Term] [Term]

*/

Data.Alts( "InLet",
           "InAppLeft",
           "InAppRight",
           "InCon",
           "InCase",
           "InSuccess",
           "InBind",
           "InBuiltin" );









/*

evaluate :: Env (Sourced String) Term -> Term -> Either String Term
evaluate denv tm = rec 3750 denv [] tm

*/





/*

matchPattern :: Pattern -> Term -> Maybe [Term]
matchPattern (Var _) v = Just [v]
matchPattern (In (ConPat c ps)) (In (Con c' as))
  | c == c' && length ps == length as =
    fmap concat (zipWithM matchPattern (map body ps) (map body as))
matchPattern (In (PrimPat x)) (In (PrimData y))
  | x == y = Just []
matchPattern _ _ = Nothing

matchPatterns :: [Pattern] -> [Term] -> Maybe [Term]
matchPatterns ps zs = fmap concat (zipWithM matchPattern ps zs)

matchClauses :: [Clause] -> [Term] -> Maybe Term
matchClauses [] _ =
  Nothing
matchClauses (Clause pscs sc:cs) vs =
  case matchPatterns (map body pscs) vs of
    Nothing -> matchClauses cs vs
    Just xs -> Just (instantiate sc xs)
    
*/



function zipWith2Proc(xs,ys,f) {
  if (xs.length !== ys.length) {
    return;
  } else {
    
    for (let i = 0; i < xs.length; i++) {
      f(xs[i],ys[i]);
    }
    
  }
}

function matchPattern(p,v) {
  return cases(p, {
    
    VarPat: function (_) { return Just([v]); },
    
    ConPat: function (c,ps) {
      return cases(v, {
        Con: function (c2,vs2) {
          if (c === c2 && ps.length === vs2.length) {
            return matchPatterns(ps,vs2);
          } else {
            return Nothing();
          }
        },
        otherwise: function () {
          return Nothing();
        }
      })
    },
    
    PrimPat: function (pd) {
      return cases(v, {
        PrimData: function (pd2) {
          return pd === pd2;
        },
        otherwise: function () {
          return Nothing();
        }
      })
    },
    
    otherwise: function () {
      return Nothing();
    }
    
  });
}

function matchPatterns (ps,vs) {
  let rs = [];
  let everNothing = false;
  
  zipWith2Proc(ps,vs, function (p,v) {
    cases(matchPattern(p,v), {
      Nothing: function () { everNothing = true; },
      Just: function (r) { rs = rs.concat(r); }
    });
  });
  
  if (everNothing) {
    return Nothing();
  } else {
    return Just(rs);
  }
}

function matchClauses(cs,vs) {
  if (0 === cs.length) {
    return Nothing();
  } else {
    return cases(cs[0], {
      Clause: function (ps, sc) {
        return cases(matchPatterns(ps,vs), {
          Nothing: function () { return matchClauses(cs.slice(1), vs); },
          Just: function (xs) { return Just(sc.apply(null,xs)); }
        });
      }
    });
  }
}



function builtin(n, ms) {
  /*
    
    addInt
    subtractInt
    multiplyInt
    divideInt
    remainderInt
    lessThanInt
    equalsInt
    intToFloat
    intToByteString
    
    addFloat
    subtractFloat
    multiplyFloat
    divideFloat
    lessThanFloat
    equalsFloat
    ceiling
    floor
    round
    
    concatenate
    drop
    take
    sha2_256
    sha3_256
    equalsByteString
    
  */
  
  ms = ms.map(m => m.args[0].args[0]);
  
  if ("addInt" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] + ms[1]);
    } else {
      return Left("Incorrect arguments for builtin addInt: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("subtractInt" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] - ms[1]);
    } else {
      return Left("Incorrect arguments for builtin subtractInt: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("multiplyInt" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] * ms[1]);
    } else {
      return Left("Incorrect arguments for builtin subtractInt: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("divideInt" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(Math.floor(ms[0] / ms[1]));
    } else {
      return Left("Incorrect arguments for builtin divideInt: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("remainderInt" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] % ms[1]);
    } else {
      return Left("Incorrect arguments for builtin remainderInt: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("lessThanInt" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] < ms[1]);
    } else {
      return Left("Incorrect arguments for builtin lessThanInt: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("equalsInt" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] === ms[1]);
    } else {
      return Left("Incorrect arguments for builtin equalsInt: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("intToFloat" === n) {
    if (1 === ms.length && typeof ms[0] === "number") {
      return Right(1.0*ms[0]);
    } else {
      return Left("Incorrect arguments for builtin intToFloat: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("intToByteString" === n) {
    // !!!! This needs to change in any real implementation.
    return Left("intToByteString is not supported at this time.");
    
  } else if ("addFloat" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] + ms[1]);
    } else {
      return Left("Incorrect arguments for builtin addFloat: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("subtractFloat" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] - ms[1]);
    } else {
      return Left("Incorrect arguments for builtin subtractFloat: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("multiplyFloat" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] * ms[1]);
    } else {
      return Left("Incorrect arguments for builtin multiplyFloat: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("divideFloat" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] / ms[1]);
    } else {
      return Left("Incorrect arguments for builtin divideFloat: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("lessThanFloat" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] < ms[1]);
    } else {
      return Left("Incorrect arguments for builtin lessThanFloat: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("equalsFloat" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[0] === ms[1]);
    } else {
      return Left("Incorrect arguments for builtin equalsFloat: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("ceiling" === n) {
    if (1 === ms.length && typeof ms[0] === "number") {
      return Right(Math.ceil(ms[0]));
    } else {
      return Left("Incorrect arguments for builtin ceiling: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("floor" === n) {
    if (1 === ms.length && typeof ms[0] === "number") {
      return Right(Math.floor(ms[0]));
    } else {
      return Left("Incorrect arguments for builtin floor: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("round" === n) {
    if (1 === ms.length && typeof ms[0] === "number") {
      return Right(Math.round(ms[0]));
    } else {
      return Left("Incorrect arguments for builtin round: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("concatenate" === n) {
    if (2 === ms.length && typeof ms[0] === "string" && typeof ms[1] === "string") {
      return Right(ms[0] + ms[1]);
    } else {
      return Left("Incorrect arguments for builtin concatenate: " + ms.map(x => show(x)).join(","));
    }
    
    
  } else if ("drop" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "number") {
      return Right(ms[1].slice(ms[0]));
    } else {
      return Left("Incorrect arguments for builtin drop: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("take" === n) {
    if (2 === ms.length && typeof ms[0] === "number" && typeof ms[1] === "string") {
      return Right(ms[1].slice(0,ms[0]));
    } else {
      return Left("Incorrect arguments for builtin take: " + ms.map(x => show(x)).join(","));
    }
    
  } else if ("sha2_256" === n) {
    // !!!! This needs to change in any real implementation.
    return Left("sha2_256 is not supported at this time.")
    
  } else if ("sha3_256" === n) {
    // !!!! This needs to change in any real implementation.
    return Left("sha3_256 is not supported at this time.")
    
  } else if ("equalsByteString" === n) {
    if (2 === ms.length && typeof ms[0] === "string" && typeof ms[1] === "string") {
      return Right(ms[0] === ms[1]);
    } else {
      return Left("Incorrect arguments for builtin equalsString: " + ms.map(x => show(x)).join(","));
    }
    
  } else {
    return Left("No builtin named " + n);
  }
}



Data.Alts( "Left", "Right" );
Data.Alts( "Nothing", "Just" );

function evaluate(denv, term) {
  
  let petrol = 3750;
  
  let stack = [];
  
  let focus = term;
  
  const REC = 0;
  const RET = 1;
  let direction = REC;
  
  while (petrol > 0) {
    petrol--;
    
    console.log("");
    console.log("Petrol: ", petrol);
    console.log("Direction: ", direction);
    console.log("Focus: ", show(focus));
    console.log("Stack size: ", stack.length);
    
    if (REC === direction) {
      
      /*
      
      rec petrol denv stk (In (Con c (m:ms))) =
        rec (petrol - 1) denv (InCon c [] (map instantiate0 ms) : stk) (instantiate0 m)
      
      rec petrol denv stk (In (Case [] cs)) =
        case matchClauses cs [] of
          Nothing ->
            Left ("Incomplete pattern match: "
                   ++ pretty (In (Case [] cs)))
          Just m'  ->
            rec (petrol - 1) denv stk m'
      
      rec petrol denv stk (In (Case (m:ms) cs)) =
        rec (petrol - 1) denv (InCase [] (map instantiate0 ms) cs : stk) (instantiate0 m)
      
      rec petrol denv stk (In (Builtin n [])) =
        case builtin n [] of
          Left err ->
            Left err
          Right m' ->
            ret (petrol - 1) denv stk m'
      rec petrol denv stk (In (Builtin n (m:ms))) =
        rec (petrol - 1) denv (InBuiltin n [] (map instantiate0 ms) : stk) (instantiate0 m)
      
      */
      
      let err = null;
      console.log(direction, show(focus));
      cases(focus, {
        
        Var: function (x) {
          direction = RET;
        },
        
        Decname: function (n) {
          if (denv[n]) {
            focus = denv[n];
            direction = RET;
          } else {
            err = "Unknown constant/defined term: " + n;
          }
        },
        
        Let: function (m, sc) {
          stack.push(InLet(sc));
          focus = m;
        },
        
        Lam: function (sc) {
          direction = RET;
        },
        
        App: function (f,x) {
          stack.push(InAppLeft(x));
          focus = f;
        },
        
        Con: function (c,ms) {
          if (0 === ms.length) {
            direction = RET;
          } else {
            stack.push(InCon(c,[],ms.slice(1)));
            focus = ms[0];
          }
        },
        
        Case: function (ms,cs) {
          if (0 === ms.length) {
            
            cases(matchClauses(cs,ms), {
              
              Nothing: function () {
                err = "Incomplete pattern match: " + show(focus);
              },
              
              Just: function (m) {
                focus = m;
              }
              
            });
            
          } else {
            stack.push(InCase([],ms.slice(1),cs));
            focus = ms[0];
          }
        },
        
        Success: function (m) {
          stack.push(InSuccess());
          focus = m;
        },
        
        Failure: function () {
          direction = RET;
        },
        
        Bind: function (m,sc) {
          stack.push(InBind(sc));
          focus = m;
        },
        
        PrimData: function (d) {
          console.log("ok");
          direction = RET;
        },
        
        Builtin: function (n,ms) {
          if (0 === ms.length) {
            
            cases(builtin(n, []), {
              
              Left: function (e) {
                err = e;
              },
              
              Right: function (m) {
                focus = m;
                direction = RET;
              }
              
            });
            
          } else {
            stack.push(InBuiltin(n,[],ms.slice(1)));
            focus = ms[0];
          }
        }
        
      });
      
      if (err) {
        return Left(err);
      }
      
    } else if (RET === direction) {
      
      /*
      
      ret :: Int -> Env (Sourced String) Term -> CKStack -> Term -> Either String Term
      ret 0 _ _ _ = Left "Out of petrol."
      ret _ _ [] tm = Right tm
      ret petrol denv (InLet sc : stk) m =
        rec (petrol - 1) denv stk (instantiate sc [m])
      ret petrol denv (InAppLeft x : stk) f =
        rec (petrol - 1) denv (InAppRight f : stk) x
      ret petrol denv (InAppRight f : stk) x =
        case f of
          In (Lam _ sc) ->
            rec (petrol - 1) denv stk (instantiate sc [x])
          _ ->
            ret (petrol - 1) denv stk (appH f x)
      ret petrol denv (InCon c revls rs : stk) m =
        case rs of
          [] -> ret (petrol - 1) denv stk (conH c (reverse (m:revls)))
          m':rs' -> rec (petrol - 1) denv (InCon c (m:revls) rs' : stk) m'
      ret petrol denv (InCase revls rs cs : stk) m =
        case rs of
          [] ->
            let ems = reverse (m:revls)
            in case matchClauses cs ems of
              Nothing ->
                Left ("Incomplete pattern match: "
                       ++ pretty (In (Case (map (scope []) ems) cs)))
              Just m'  ->
                rec (petrol - 1) denv stk m'
          m':rs' -> rec (petrol - 1) denv (InCase (m:revls) rs' cs : stk) m'
      ret petrol denv (InSuccess : stk) m =
        ret (petrol - 1) denv stk (successH m)
      ret petrol denv (InBind sc : stk) m =
        case m of
          In (Failure a) ->
            ret (petrol - 1) denv stk (failureH a)
          In (Success m') ->
            rec (petrol - 1) denv stk (instantiate sc [instantiate0 m'])
          _ ->
            Left ("Cannot bind a non-computation: " ++ pretty m)
      ret petrol denv (InBuiltin n revls rs : stk) m =
        case rs of
          [] -> case builtin n (reverse (m:revls)) of
            Left err ->
              Left err
            Right m' ->
              ret (petrol - 1) denv stk m'
          m':rs' ->
            rec (petrol - 1) denv (InBuiltin n (m:revls) rs' : stk) m'
      
      */
      
      if (0 === stack.length) {
        
        return Right(focus);
        
      } else {
        
        let frame = stack.pop();
        let err = null;
        
        cases(frame, {
          
          InLet: function (sc) {
            direction = REC;
            focus = sc(focus);
          },
          
          InAppLeft: function (x) {
            direction = REC;
            stack.push(InAppRight(focus));
            focus = x;
          },
          
          InAppRight: function (f) {
            cases(f, {
              
              Lam: function (b) {
                direction = REC;
                focus = f.args[0](focus);
              },
              
              otherwise: function () {
                focus = App(f,focus);
              }
            })
            
          },
          
          InCon: function (c,ls,rs) {
            if (0 === rs.length) {
              ls.push(focus);
              focus = Con(c,ls);
            } else {
              
              direction = REC;
              let m = rs.pop();
              ls.push(focus);
              stack.push(InCon(c,ls,rs));
              focus = m;
              
            }
          },
          
          InCase: function (ls,rs,cs) {
            if (0 === rs.length) {
              ls.push(focus);
              cases(matchClauses(cs,ls), {
                
                Nothing: function () {
                  err = "Incomplete pattern match: " + show(focus);
                },
                
                Just: function (m) {
                  focus = m;
                }
                
              });
              
            } else {
              
              direction = REC;
              let m = rs.pop();
              ls.push(focus);
              stack.push(InCase(ls,rs,cs));
              focus = m;
              
            }
          },
          
          InSuccess: function (m) {
            
            focus = Success(m);
            
          },
          
          InBind: function (sc) {
            
            direction = REC;
            focus = sc(focus);
            
          },
          
          InBuiltin: function (n,ls,rs) {
            
            if (0 === rs.length) {
              
              ls.push(focus);
              cases(builtin(n,ls), {
                
                Left: function (e) {
                  err = e;
                },
                
                Right: function (m) {
                  focus = m;
                }
                
              });
              
            } else {
              
              direction = REC;
              let m = rs.pop();
              ls.push(focus);
              stack.push(InBuiltin(n,ls,rs));
              focus = m;
              
            }
            
          }
          
        });
        
        if (err) {
          return Left(err);
        }
        
      }
      
      
    }
    
  }
  
  return Left("Out of petrol.");
  
}