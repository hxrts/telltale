// Cytoscape.js bridge for the Telltale viewer graph canvas.
// Called from Rust/WASM via wasm-bindgen JS interop.
//
// Color values use the same oklch palette as the Telltale design tokens:
//   --background:       oklch(0.18 0 0)
//   --foreground:       oklch(0.97 0 0)
//   --primary:          oklch(0.78 0 0)
//   --secondary:        oklch(0.30 0 0)
//   --muted-foreground: oklch(0.68 0 0)
//   --border:           oklch(0.35 0 0)
//   --accent:           oklch(0.30 0 0)

window.__tt_cytoscape = null;

window.__tt_init_graph = function (containerId) {
  var container = document.getElementById(containerId);
  if (!container || !window.cytoscape) return;

  if (window.__tt_cytoscape) {
    window.__tt_cytoscape.destroy();
  }

  window.__tt_cytoscape = cytoscape({
    container: container,
    style: [
      {
        selector: "node",
        style: {
          "label": "data(label)",
          "background-color": "oklch(0.30 0 0)",
          "color": "oklch(0.68 0 0)",
          "text-valign": "bottom",
          "text-halign": "center",
          "font-size": "9px",
          "font-family": "'JetBrains Mono', monospace",
          "text-margin-y": 5,
          "width": 20,
          "height": 20,
          "border-width": 1,
          "border-color": "oklch(0.35 0 0)",
          "transition-property": "background-color, border-color, opacity",
          "transition-duration": "150ms"
        }
      },
      {
        selector: "node:selected",
        style: {
          "background-color": "oklch(0.78 0 0)",
          "border-color": "oklch(0.55 0 0)",
          "border-width": 2,
          "color": "oklch(0.97 0 0)"
        }
      },
      {
        selector: "node.active-step",
        style: {
          "background-color": "oklch(0.78 0 0)",
          "border-color": "oklch(0.55 0 0)",
          "border-width": 1.5,
          "color": "oklch(0.97 0 0)"
        }
      },
      {
        selector: "node.dimmed",
        style: {
          "opacity": 0.15
        }
      },
      {
        selector: "edge",
        style: {
          "width": 1,
          "line-color": "oklch(0.35 0 0)",
          "target-arrow-color": "oklch(0.35 0 0)",
          "target-arrow-shape": "triangle",
          "arrow-scale": 0.6,
          "curve-style": "bezier",
          "label": "data(label)",
          "font-size": "7px",
          "font-family": "'JetBrains Mono', monospace",
          "color": "oklch(0.50 0 0)",
          "text-rotation": "autorotate",
          "text-margin-y": -6,
          "transition-property": "line-color, opacity",
          "transition-duration": "150ms"
        }
      },
      {
        selector: "edge:selected",
        style: {
          "line-color": "oklch(0.55 0 0)",
          "target-arrow-color": "oklch(0.55 0 0)",
          "width": 1.5
        }
      },
      {
        selector: "edge.dimmed",
        style: {
          "opacity": 0.08
        }
      }
    ],
    layout: {
      name: "cose",
      animate: false,
      randomize: false,
      nodeOverlap: 20,
      idealEdgeLength: 80,
      nodeRepulsion: 8000,
      gravity: 0.25
    },
    minZoom: 0.3,
    maxZoom: 3,
    wheelSensitivity: 0.2,
    boxSelectionEnabled: false,
    selectionType: "single"
  });
};

window.__tt_update_graph = function (nodesJson, edgesJson) {
  var cy = window.__tt_cytoscape;
  if (!cy) return;

  var nodes = JSON.parse(nodesJson);
  var edges = JSON.parse(edgesJson);

  cy.elements().remove();

  var elements = [];
  for (var i = 0; i < nodes.length; i++) {
    var node = nodes[i];
    elements.push({
      group: "nodes",
      data: { id: node.id, label: node.label, category: node.category, step: node.step }
    });
  }
  for (var j = 0; j < edges.length; j++) {
    var edge = edges[j];
    elements.push({
      group: "edges",
      data: {
        id: edge.from + "->" + edge.to,
        source: edge.from,
        target: edge.to,
        label: edge.label,
        step: edge.step
      }
    });
  }

  cy.add(elements);
  cy.layout({
    name: "cose",
    animate: true,
    animationDuration: 250,
    animationEasing: "ease-out",
    randomize: false,
    nodeOverlap: 20,
    idealEdgeLength: 80,
    nodeRepulsion: 8000,
    gravity: 0.25
  }).run();
};

window.__tt_filter_graph_step = function (maxStepStr) {
  var cy = window.__tt_cytoscape;
  if (!cy) return;

  var maxStep = parseInt(maxStepStr, 10);

  cy.nodes().forEach(function (node) {
    var step = node.data("step");
    node.removeClass("dimmed active-step");
    if (step !== undefined && step !== null) {
      if (step > maxStep) {
        node.addClass("dimmed");
      } else if (step === maxStep) {
        node.addClass("active-step");
      }
    }
  });

  cy.edges().forEach(function (edge) {
    var step = edge.data("step");
    edge.removeClass("dimmed");
    if (step !== undefined && step !== null && step > maxStep) {
      edge.addClass("dimmed");
    }
  });
};
