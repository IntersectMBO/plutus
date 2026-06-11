(let
  (nonrec)
  (datatypebind
    (datatype (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit))
  )
  (lam ds (con data) (lam ds (con data) (lam ds (con data) Unit)))
)