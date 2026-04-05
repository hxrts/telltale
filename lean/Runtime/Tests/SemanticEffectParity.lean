import Lean.Data.Json

set_option autoImplicit false

open Lean (Json)

structure ReducedSemanticEffectFixture where
  name : String
  effectKind : String
  lifecycle : String
  interfaceName : String
  operationName : String
  publicationMaterialized : Bool
  outputPredicate : Option String
  deriving Repr, Inhabited

def fixtureJson (fixture : ReducedSemanticEffectFixture) : Json :=
  Json.mkObj <|
    [ ("name", Json.str fixture.name)
    , ("effect_kind", Json.str fixture.effectKind)
    , ("lifecycle", Json.str fixture.lifecycle)
    , ("interface_name", Json.str fixture.interfaceName)
    , ("operation_name", Json.str fixture.operationName)
    , ("publication_materialized", Json.bool fixture.publicationMaterialized)
    , ("output_predicate",
        match fixture.outputPredicate with
        | some predicate => Json.str predicate
        | none => Json.null)
    ]

def fixtures : List ReducedSemanticEffectFixture :=
  [ { name := "blocked_send"
    , effectKind := "send_decision"
    , lifecycle := "blocked"
    , interfaceName := "Transport"
    , operationName := "sendDecision"
    , publicationMaterialized := false
    , outputPredicate := none
    }
  , { name := "send_publication"
    , effectKind := "send_decision"
    , lifecycle := "succeeded"
    , interfaceName := "Transport"
    , operationName := "sendDecision"
    , publicationMaterialized := true
    , outputPredicate := some "machine.replay.internal_effects"
    }
  , { name := "output_condition_hint"
    , effectKind := "output_condition_hint"
    , lifecycle := "succeeded"
    , interfaceName := "Runtime"
    , operationName := "outputConditionHint"
    , publicationMaterialized := false
    , outputPredicate := some "machine.replay.internal_effects"
    }
  , { name := "wal_sync"
    , effectKind := "wal_sync"
    , lifecycle := "succeeded"
    , interfaceName := "Wal"
    , operationName := "sync"
    , publicationMaterialized := false
    , outputPredicate := none
    }
  ]

def main : IO Unit := do
  let payload := Json.mkObj
    [ ("schema_version", Json.str "semantic_effect_parity_v1")
    , ("fixtures", Json.arr <| fixtures.map fixtureJson |>.toArray)
    ]
  IO.println payload.compress
