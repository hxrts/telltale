// Cytoscape.js bridge for the Telltale viewer graph canvas.
// Called from Rust/WASM via wasm-bindgen JS interop.
//
// Cytoscape renders to <canvas>, not CSS, so oklch() is not supported.
// Colors are hex equivalents of the app design tokens:
//   --background:       #2b2b2b
//   --foreground:       #f5f5f5
//   --primary:          #bfbfbf
//   --secondary:        #474747
//   --muted-foreground: #a3a3a3
//   --border:           #545454
//   --accent:           #474747
//   --ring:             #808080

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
          "background-color": "#474747",
          "color": "#a3a3a3",
          "text-valign": "bottom",
          "text-halign": "center",
          "font-size": "9px",
          "font-family": "'JetBrains Mono', monospace",
          "text-margin-y": 5,
          "text-wrap": "ellipsis",
          "text-max-width": "80px",
          "width": 20,
          "height": 20,
          "border-width": 1,
          "border-color": "#545454",
          "transition-property": "background-color, border-color, opacity",
          "transition-duration": "150ms"
        }
      },
      {
        selector: "node:selected",
        style: {
          "background-color": "#bfbfbf",
          "border-color": "#808080",
          "border-width": 2,
          "color": "#f5f5f5"
        }
      },
      {
        selector: "node.active-step",
        style: {
          "background-color": "#bfbfbf",
          "border-color": "#808080",
          "border-width": 1.5,
          "color": "#f5f5f5"
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
          "line-color": "#545454",
          "target-arrow-color": "#545454",
          "target-arrow-shape": "triangle",
          "arrow-scale": 0.6,
          "curve-style": "bezier",
          "label": "data(label)",
          "font-size": "7px",
          "font-family": "'JetBrains Mono', monospace",
          "color": "#777777",
          "text-rotation": "autorotate",
          "text-margin-y": -6,
          "text-background-color": "#2b2b2b",
          "text-background-opacity": 0.8,
          "text-background-padding": "2px",
          "transition-property": "line-color, opacity",
          "transition-duration": "150ms"
        }
      },
      {
        selector: "edge:selected",
        style: {
          "line-color": "#808080",
          "target-arrow-color": "#808080",
          "width": 1.5,
          "color": "#a3a3a3"
        }
      },
      {
        selector: "edge.dimmed",
        style: {
          "opacity": 0.08
        }
      }
    ],
    layout: { name: "preset" },
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

  // Run force-directed layout with randomized initial positions
  cy.layout({
    name: "cose",
    animate: true,
    animationDuration: 400,
    animationEasing: "ease-out",
    randomize: true,
    nodeOverlap: 30,
    idealEdgeLength: function () { return 100; },
    nodeRepulsion: function () { return 10000; },
    gravity: 0.3,
    numIter: 500,
    fit: true,
    padding: 30
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
