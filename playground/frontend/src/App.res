// SPDX-License-Identifier: AGPL-3.0-or-later
// Main Ephapax Playground Application

module Mode = {
  type t = Affine | Linear

  let toString = mode =>
    switch mode {
    | Affine => "affine"
    | Linear => "linear"
    }

  let fromString = str =>
    switch str {
    | "linear" => Linear
    | _ => Affine
    }
}

module Example = {
  type t = {
    id: string,
    name: string,
    description: string,
    filename: string,
  }

  let examples = [
    {
      id: "hello",
      name: "Hello World",
      description: "Basic function returning 42",
      filename: "01-hello-world.eph",
    },
    {
      id: "affine-drop",
      name: "Affine: Implicit Drop",
      description: "Shows implicit dropping in affine mode",
      filename: "10-affine-drop.eph",
    },
    {
      id: "linear-demo",
      name: "Linear: Type Checking Demo",
      description: "Validates linear type rules",
      filename: "20-linear-demo.eph",
    },
    {
      id: "linear-explicit",
      name: "Linear: Explicit Drop",
      description: "Correct linear code with explicit consumption",
      filename: "21-linear-explicit.eph",
    },
    {
      id: "comparison",
      name: "Affine vs Linear",
      description: "Side-by-side comparison of modes",
      filename: "30-comparison.eph",
    },
  ]
}

type compileState =
  | Idle
  | Compiling
  | Success({wasm: string, sexpr: string})
  | Error({errors: array<string>, warnings: option<array<string>>})

type state = {
  mode: Mode.t,
  code: string,
  compileState: compileState,
  selectedExample: option<string>,
  outputTab: string,
}

type action =
  | SetMode(Mode.t)
  | SetCode(string)
  | SetCompileState(compileState)
  | SelectExample(string)
  | SetOutputTab(string)
  | LoadExample(string)

let reducer = (state, action) =>
  switch action {
  | SetMode(mode) => {...state, mode: mode}
  | SetCode(code) => {...state, code: code}
  | SetCompileState(compileState) => {...state, compileState: compileState}
  | SelectExample(id) => {...state, selectedExample: Some(id)}
  | SetOutputTab(tab) => {...state, outputTab: tab}
  | LoadExample(code) => {...state, code: code}
  }

@react.component
let make = () => {
  let (state, dispatch) = React.useReducer(
    reducer,
    {
      mode: Affine,
      code: "// SPDX-License-Identifier: EUPL-1.2\n// Welcome to Ephapax Playground!\n// Select an example from the right panel to get started.\n\nfn main() -> i32 {\n    42\n}",
      compileState: Idle,
      selectedExample: None,
      outputTab: "output",
    },
  )

  // Load example when selected
  let loadExample = exampleId => {
    dispatch(SelectExample(exampleId))

    // In real implementation, fetch from /examples/{filename}
    // For now, just update the editor with placeholder
    let example = Example.examples->Array.find(ex => ex.id == exampleId)
    switch example {
    | Some(ex) => {
        // TODO: Fetch actual file content
        let placeholder = `// Loading ${ex.filename}...\n// (Would fetch from server in real implementation)`
        dispatch(LoadExample(placeholder))
      }
    | None => ()
    }
  }

  // Compile function
  let compile = async () => {
    dispatch(SetCompileState(Compiling))

    try {
      let response = await Fetch.fetch(
        "/api/compile",
        {
          method: #POST,
          headers: Headers.fromObject({
            "Content-Type": "application/json",
          }),
          body: JSON.stringifyAny({
            "code": state.code,
            "mode": Mode.toString(state.mode),
          })->Option.getOr(""),
        },
      )

      let json = await response->Response.json

      // Parse response
      let success = json->JSON.Decode.object
        ->Option.flatMap(obj => obj->Dict.get("success"))
        ->Option.flatMap(JSON.Decode.bool)
        ->Option.getOr(false)

      if success {
        let wasm = json->JSON.Decode.object
          ->Option.flatMap(obj => obj->Dict.get("wasm"))
          ->Option.flatMap(JSON.Decode.string)
          ->Option.getOr("")

        let sexpr = json->JSON.Decode.object
          ->Option.flatMap(obj => obj->Dict.get("sexpr"))
          ->Option.flatMap(JSON.Decode.string)
          ->Option.getOr("")

        dispatch(SetCompileState(Success({wasm, sexpr})))
      } else {
        let errors = json->JSON.Decode.object
          ->Option.flatMap(obj => obj->Dict.get("errors"))
          ->Option.flatMap(JSON.Decode.array)
          ->Option.map(arr => arr->Array.filterMap(JSON.Decode.string))
          ->Option.getOr([])

        let warnings = json->JSON.Decode.object
          ->Option.flatMap(obj => obj->Dict.get("warnings"))
          ->Option.flatMap(JSON.Decode.array)
          ->Option.map(arr => arr->Array.filterMap(JSON.Decode.string))

        dispatch(SetCompileState(Error({errors, warnings})))
      }
    } catch {
    | exn => {
        let message = exn->Exn.message->Option.getOr("Unknown error")
        dispatch(SetCompileState(Error({errors: [message], warnings: None})))
      }
    }
  }

  <div>
    // Header
    <div className="header">
      <div>
        <h1> {"Ephapax Playground"->React.string} </h1>
        <span className="header-subtitle">
          {"Linear & Affine Type Systems"->React.string}
        </span>
      </div>
      <div className="mode-toggle">
        <button
          className={`mode-button ${state.mode == Affine ? "active" : ""}`}
          onClick={_ => dispatch(SetMode(Affine))}>
          {"Affine Mode"->React.string}
        </button>
        <button
          className={`mode-button ${state.mode == Linear ? "active linear" : ""}`}
          onClick={_ => dispatch(SetMode(Linear))}>
          {"Linear Mode"->React.string}
        </button>
      </div>
    </div>
    // Main Container
    <div className="main-container">
      // Editor Panel
      <div className="editor-panel">
        <div className="panel-header">
          <span className="panel-title"> {"Code Editor"->React.string} </span>
          <button
            className="compile-button"
            disabled={state.compileState == Compiling}
            onClick={_ => compile()->ignore}>
            {(state.compileState == Compiling ? "Compiling..." : "Compile")->React.string}
          </button>
        </div>
        <div className="editor-wrapper">
          <textarea
            value={state.code}
            onChange={e => {
              let value = ReactEvent.Form.target(e)["value"]
              dispatch(SetCode(value))
            }}
            style={ReactDOM.Style.make(
              ~width="100%",
              ~height="100%",
              ~padding="1rem",
              ~background="var(--bg-primary)",
              ~color="var(--text-primary)",
              ~border="none",
              ~fontFamily="'Consolas', 'Monaco', monospace",
              ~fontSize="14px",
              ~resize="none",
              (),
            )}
          />
        </div>
      </div>
      // Examples Sidebar
      <div className="examples-panel">
        <div className="panel-header">
          <span className="panel-title"> {"Examples"->React.string} </span>
        </div>
        {Example.examples
        ->Array.map(example =>
          <div
            key={example.id}
            className={`example-item ${state.selectedExample == Some(example.id) ? "active" : ""}`}
            onClick={_ => loadExample(example.id)}>
            <div className="example-name"> {example.name->React.string} </div>
            <div className="example-description"> {example.description->React.string} </div>
          </div>
        )
        ->React.array}
      </div>
      // Output Panel
      <div className="output-panel">
        <div className="output-tabs">
          <button
            className={`output-tab ${state.outputTab == "output" ? "active" : ""}`}
            onClick={_ => dispatch(SetOutputTab("output"))}>
            {"Output"->React.string}
          </button>
          <button
            className={`output-tab ${state.outputTab == "sexpr" ? "active" : ""}`}
            onClick={_ => dispatch(SetOutputTab("sexpr"))}>
            {"S-Expression IR"->React.string}
          </button>
          <button
            className={`output-tab ${state.outputTab == "wasm" ? "active" : ""}`}
            onClick={_ => dispatch(SetOutputTab("wasm"))}>
            {"WebAssembly"->React.string}
          </button>
        </div>
        <div className="output-content">
          {switch (state.compileState, state.outputTab) {
          | (Idle, _) => <div> {"Click 'Compile' to see results"->React.string} </div>
          | (Compiling, _) =>
            <div className="loading">
              <div className="spinner" />
              {"Compiling..."->React.string}
            </div>
          | (Success({wasm, sexpr}), "output") =>
            <div className="success-message">
              <div> {"✓ Compilation successful!"->React.string} </div>
              <div> {`WASM size: ${String.length(wasm)} bytes`->React.string} </div>
            </div>
          | (Success({sexpr}), "sexpr") => <pre> {sexpr->React.string} </pre>
          | (Success({wasm}), "wasm") =>
            <div>
              <div> {`Base64-encoded WASM (${String.length(wasm)} bytes):`->React.string} </div>
              <pre> {wasm->React.string} </pre>
            </div>
          | (Error({errors, warnings}), _) =>
            <div>
              {errors
              ->Array.map(err =>
                <div key={err} className="error-message"> {`✗ ${err}`->React.string} </div>
              )
              ->React.array}
              {warnings
              ->Option.map(warns =>
                warns
                ->Array.map(warn =>
                  <div key={warn} className="warning-message"> {`⚠ ${warn}`->React.string} </div>
                )
                ->React.array
              )
              ->Option.getOr(React.null)}
            </div>
          | _ => React.null
          }}
        </div>
      </div>
    </div>
  </div>
}

// Mount the app
switch ReactDOM.querySelector("#root") {
| Some(root) => ReactDOM.render(<App />, root)
| None => Console.error("Root element not found")
}
