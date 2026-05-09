
import ProofWidgets
open scoped ProofWidgets.Jsx

-- This command tells Lean to render a custom UI in the Infoview.
-- Click on the '#html' below to see the result!
#html
  <div style={json% {
    backgroundColor: "#f9f9f9",
    padding: "20px",
    borderRadius: "8px",
    border: "1px solid #ddd",
    fontFamily: "sans-serif"
  }}>
    <h2 style={json% { color: "#2c3e50", margin: "0 0 10px 0" }}>Origami Tactic Test</h2>
    <p style={json% { color: "#666", fontSize: "14px" }}>Verification of SVG rendering for construction axioms.</p>

    <svg width="300" height="300" style={json% { backgroundColor: "white", border: "1px solid #333", boxShadow: "0 2px 4px rgba(0,0,0,0.1)" }}>
      <rect x="0" y="0" width="300" height="300" fill="none" stroke="#ccc" strokeWidth="1" />

      <line x1="50" y1="20" x2="250" y2="280" stroke="#3498db" strokeWidth="3" strokeDasharray="5,5" />

      <circle cx="150" cy="150" r="6" fll="#e74c3c" />
      <text x="160" y="145" fontSize="12" fill="#e74c3c" fontWeight="bold">P1</text>

      <text x="10" y="290" fontSize="10" fill="#999">Status: ProofWidgets Loaded</text>
    </svg>

    <div style={json% { marginTop: "15px", padding: "8px", backgroundColor: "#e8f8f5", borderRadius: "4px", color: "#27ae60", fontSize: "13px" }}>
      <b>Success:</b> If you see the blue dashed line and red point, your GUI infrastructure is ready.
    </div>
  </div>
