#!/usr/bin/env python3
"""
html_diff_generator.py — Beautiful HTML Report Generator for CERES vs SPIKE
============================================================================
Generates interactive, color-coded HTML comparison reports with:
  ✅ Search and filtering capabilities
  ✅ Pagination for large logs
  ✅ Interactive pie/bar charts
  ✅ Export options (CSV, JSON)
  ✅ Dark/Light theme toggle
  ✅ Keyboard shortcuts
  ✅ Collapsible sections
  ✅ First N errors quick navigation
"""
from datetime import datetime
from colorama import Fore, Style
import json
import html as html_escape

# Check for quiet mode from parent module
try:
    from compare_logs import QUIET
except ImportError:
    QUIET = False

def entries_equal(a, b):
    """Check if two log entries have matching PC and INST"""
    return a[0] == b[0] and a[1] == b[1]


def parse_bp_stats(bp_stats_path):
    """
    Parse bp_stats.log file and extract branch predictor statistics.
    
    Args:
        bp_stats_path: Path to bp_stats.log file
    
    Returns:
        Dictionary with BP statistics or None if file doesn't exist
    """
    import re
    import os
    
    if not bp_stats_path or not os.path.exists(bp_stats_path):
        return None
    
    stats = {
        "total_branches": 0,
        "correct": 0,
        "mispred": 0,
        "accuracy": 0.0,
        "jal_total": 0,
        "jal_correct": 0,
        "jal_accuracy": 0.0,
        "jalr_total": 0,
        "jalr_correct": 0,
        "jalr_accuracy": 0.0,
        "ras_total": 0,
        "ras_correct": 0,
        "ras_accuracy": 0.0,
        "ibtc_total": 0,
        "ibtc_correct": 0,
        "ibtc_accuracy": 0.0,
        "cond_total": 0,
        "cond_correct": 0,
        "cond_mispred": 0,
        "cond_accuracy": 0.0,
    }
    
    try:
        with open(bp_stats_path, 'r', errors='ignore') as f:
            content = f.read()
            
            # Parse Total Control Transfers
            match = re.search(r'Total Control Transfers\s*:\s*(\d+)', content)
            if match:
                stats["total_branches"] = int(match.group(1))
            
            # Parse Correct Predictions with percentage
            match = re.search(r'Correct Predictions\s*:\s*(\d+)\s*\(\s*([\d.]+)%\)', content)
            if match:
                stats["correct"] = int(match.group(1))
                stats["accuracy"] = float(match.group(2))
            
            # Parse Mispredictions
            match = re.search(r'Mispredictions\s*:\s*(\d+)', content)
            if match:
                stats["mispred"] = int(match.group(1))
            
            # Parse JAL statistics - Total and Correct on separate lines
            jal_section = re.search(r'JAL \(Direct Jump\).*?Total\s*:\s*(\d+).*?Correct\s*:\s*(\d+)\s*\(\s*([\d.]+)%\)', content, re.DOTALL)
            if jal_section:
                stats["jal_total"] = int(jal_section.group(1))
                stats["jal_correct"] = int(jal_section.group(2))
                stats["jal_accuracy"] = float(jal_section.group(3))
            
            # Parse JALR statistics
            jalr_section = re.search(r'JALR \(Indirect Jump\).*?Total\s*:\s*(\d+).*?Correct\s*:\s*(\d+)\s*\(\s*([\d.]+)%\)', content, re.DOTALL)
            if jalr_section:
                stats["jalr_total"] = int(jalr_section.group(1))
                stats["jalr_correct"] = int(jalr_section.group(2))
                stats["jalr_accuracy"] = float(jalr_section.group(3))
            
            # Parse RAS Predictions
            match = re.search(r'RAS Predictions\s*:\s*(\d+)\s*\(\s*([\d.]+)%\s*accurate\)', content)
            if match:
                stats["ras_total"] = int(match.group(1))
                stats["ras_accuracy"] = float(match.group(2))
                if stats["ras_total"] > 0:
                    stats["ras_correct"] = int(stats["ras_total"] * stats["ras_accuracy"] / 100)
            
            # Parse IBTC Predictions
            match = re.search(r'IBTC Predictions\s*:\s*(\d+)\s*\(\s*([\d.]+)%\s*accurate\)', content)
            if match:
                stats["ibtc_total"] = int(match.group(1))
                stats["ibtc_accuracy"] = float(match.group(2))
                if stats["ibtc_total"] > 0:
                    stats["ibtc_correct"] = int(stats["ibtc_total"] * stats["ibtc_accuracy"] / 100)
            
            # Parse Conditional Branch statistics
            cond_section = re.search(r'Conditional Branch.*?Total\s*:\s*(\d+).*?Correct\s*:\s*(\d+)\s*\(\s*([\d.]+)%\).*?Mispredicted\s*:\s*(\d+)', content, re.DOTALL)
            if cond_section:
                stats["cond_total"] = int(cond_section.group(1))
                stats["cond_correct"] = int(cond_section.group(2))
                stats["cond_accuracy"] = float(cond_section.group(3))
                stats["cond_mispred"] = int(cond_section.group(4))
            
    except Exception as e:
        if not QUIET:
            print(f"Warning: Could not parse bp_stats.log: {e}")
        return None
    
    return stats


def generate_html_diff(rtl, spike, html_path, stats, disasm_map=None, 
                      pass_addr=None, fail_addr=None, test_name=None, bp_stats_path=None):
    """
    Generate beautiful interactive HTML diff report with enhanced information.
    
    Args:
        rtl: List of RTL log entries (pc, inst, rest, line)
        spike: List of Spike log entries (pc, inst, rest, line)
        html_path: Output HTML file path
        stats: Dictionary of comparison statistics
        disasm_map: Dictionary mapping PC to (inst_hex, disassembly)
        pass_addr: Test pass address (hex value)
        fail_addr: Test fail address (hex value)
        test_name: Name of the test being compared
        bp_stats_path: Path to bp_stats.log file for branch predictor statistics
    """
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    
    # Parse branch predictor stats if available
    bp_stats = parse_bp_stats(bp_stats_path)
    
    # Calculate detailed statistics
    total_cycles = max(len(rtl), len(spike))
    match_rate = (stats["match"] / total_cycles * 100) if total_cycles > 0 else 0
    
    # Build test info section
    test_info_html = ""
    if test_name:
        test_info_html += f'<div class="subtitle test-name">Test: <strong>{test_name}</strong></div>'
    if pass_addr is not None:
        test_info_html += f'<div class="subtitle pass-info">✅ Pass Address: <strong>0x{pass_addr:08x}</strong></div>'
    if fail_addr is not None:
        test_info_html += f'<div class="subtitle fail-info">❌ Fail Address: <strong>0x{fail_addr:08x}</strong></div>'
    
    # Prepare data for JavaScript
    rows_data = []
    first_error = -1
    error_indices = []
    
    maxlen = max(len(rtl), len(spike))
    for i in range(maxlen):
        rtl_entry = rtl[i] if i < len(rtl) else None
        spike_entry = spike[i] if i < len(spike) else None
        
        # Determine status
        if rtl_entry and spike_entry:
            if entries_equal(rtl_entry, spike_entry):
                if rtl_entry[2].replace(" ","") == spike_entry[2].replace(" ",""):
                    status = "match"
                else:
                    status = "reg-warn"
                    if first_error == -1:
                        first_error = i
                    error_indices.append(i)
            else:
                status = "mismatch"
                if first_error == -1:
                    first_error = i
                error_indices.append(i)
        elif rtl_entry:
            status = "extra-rtl"
            error_indices.append(i)
        else:
            status = "extra-spike"
            error_indices.append(i)
        
        # Get disassembly
        disasm_str = ""
        if disasm_map and rtl_entry and rtl_entry[0] in disasm_map:
            _, disasm_str = disasm_map[rtl_entry[0]]
        
        # Check pass/fail highlight
        addr_highlight = ""
        if rtl_entry:
            if pass_addr is not None and rtl_entry[0] == pass_addr:
                addr_highlight = "pass"
            elif fail_addr is not None and rtl_entry[0] == fail_addr:
                addr_highlight = "fail"
        
        row = {
            "idx": i,
            "status": status,
            "highlight": addr_highlight,
            "rtl": {
                "pc": f"0x{rtl_entry[0]:08x}" if rtl_entry else "",
                "inst": f"0x{rtl_entry[1]:08x}" if rtl_entry else "",
                "reg": html_escape.escape(rtl_entry[2]) if rtl_entry else ""
            } if rtl_entry else None,
            "spike": {
                "pc": f"0x{spike_entry[0]:08x}" if spike_entry else "",
                "inst": f"0x{spike_entry[1]:08x}" if spike_entry else "",
                "reg": html_escape.escape(spike_entry[2]) if spike_entry else ""
            } if spike_entry else None,
            "disasm": html_escape.escape(disasm_str) if disasm_str else ""
        }
        rows_data.append(row)
    
    # Convert to JSON for JavaScript
    rows_json = json.dumps(rows_data)
    stats_json = json.dumps(stats)
    error_indices_json = json.dumps(error_indices[:100])  # First 100 errors
    bp_stats_json = json.dumps(bp_stats) if bp_stats else "null"
    
    html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>CERES vs SPIKE - {test_name or 'Commit Log Comparison'}</title>
    <style>
        :root {{
            /* Dark theme (default) */
            --bg-primary: #1e1e2e;
            --bg-secondary: #2a2a3e;
            --bg-tertiary: #3a3a4e;
            --text-primary: #e0e0e0;
            --text-secondary: #a0a0a0;
            --accent: #667eea;
            --accent-hover: #5568d3;
            --match: #50fa7b;
            --mismatch: #ff5555;
            --warning: #f1fa8c;
            --info: #8be9fd;
            --pc-color: #ff79c6;
            --inst-color: #bd93f9;
            --reg-color: #8be9fd;
            --border-color: #3a3a4e;
            --header-bg: linear-gradient(135deg, #434343 0%, #000000 100%);
            --body-bg: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        }}
        
        [data-theme="light"] {{
            --bg-primary: #ffffff;
            --bg-secondary: #f5f5f5;
            --bg-tertiary: #e0e0e0;
            --text-primary: #333333;
            --text-secondary: #666666;
            --accent: #5568d3;
            --accent-hover: #4458c3;
            --match: #28a745;
            --mismatch: #dc3545;
            --warning: #ffc107;
            --info: #17a2b8;
            --pc-color: #d63384;
            --inst-color: #6f42c1;
            --reg-color: #0d6efd;
            --border-color: #dee2e6;
            --header-bg: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            --body-bg: linear-gradient(135deg, #f5f7fa 0%, #c3cfe2 100%);
        }}
        
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}
        
        body {{
            font-family: 'JetBrains Mono', 'Fira Code', 'Consolas', monospace;
            background: var(--body-bg);
            color: var(--text-primary);
            padding: 20px;
            line-height: 1.6;
            min-height: 100vh;
        }}
        
        .container {{
            max-width: 1900px;
            margin: 0 auto;
            background: var(--bg-primary);
            border-radius: 12px;
            box-shadow: 0 8px 32px rgba(0, 0, 0, 0.3);
            overflow: hidden;
        }}
        
        header {{
            background: var(--header-bg);
            padding: 25px 30px;
            text-align: center;
            border-bottom: 3px solid var(--accent);
            position: relative;
        }}
        
        header h1 {{
            font-size: 2.2em;
            color: #fff;
            text-shadow: 2px 2px 4px rgba(0,0,0,0.5);
            margin-bottom: 8px;
        }}
        
        .subtitle {{
            color: #a0a0a0;
            font-size: 1em;
        }}
        
        .test-name {{ color: var(--info); margin-top: 12px; }}
        .pass-info {{ color: var(--match); font-size: 0.95em; }}
        .fail-info {{ color: var(--mismatch); font-size: 0.95em; }}
        
        .theme-toggle {{
            position: absolute;
            top: 20px;
            right: 20px;
            background: rgba(255,255,255,0.1);
            border: 1px solid rgba(255,255,255,0.2);
            color: #fff;
            padding: 8px 15px;
            border-radius: 20px;
            cursor: pointer;
            font-size: 0.9em;
            transition: all 0.3s;
        }}
        
        .theme-toggle:hover {{
            background: rgba(255,255,255,0.2);
        }}
        
        /* Stats Container with Charts */
        .stats-section {{
            display: grid;
            grid-template-columns: 1fr 300px;
            gap: 20px;
            padding: 20px;
            background: var(--bg-secondary);
            border-bottom: 2px solid var(--border-color);
        }}
        
        .stats-container {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
            gap: 12px;
        }}
        
        .stat-card {{
            background: var(--bg-primary);
            padding: 15px;
            border-radius: 8px;
            text-align: center;
            border: 2px solid var(--border-color);
            transition: transform 0.2s, border-color 0.2s;
        }}
        
        .stat-card:hover {{
            transform: translateY(-2px);
            border-color: var(--accent);
        }}
        
        .stat-label {{
            color: var(--text-secondary);
            font-size: 0.8em;
            text-transform: uppercase;
            letter-spacing: 1px;
            margin-bottom: 5px;
        }}
        
        .stat-value {{
            font-size: 1.6em;
            font-weight: bold;
        }}
        
        .stat-match {{ color: var(--match); }}
        .stat-mismatch {{ color: var(--mismatch); }}
        .stat-warning {{ color: var(--warning); }}
        .stat-info {{ color: var(--info); }}
        
        /* BP Stats Section */
        .bp-stats-section {{
            padding: 20px;
            background: var(--bg-secondary);
            border-bottom: 2px solid var(--border-color);
        }}
        
        .bp-stats-header {{
            display: flex;
            align-items: center;
            gap: 10px;
            margin-bottom: 15px;
            cursor: pointer;
        }}
        
        .bp-stats-header h3 {{
            color: var(--info);
            font-size: 1.1em;
            margin: 0;
        }}
        
        .bp-stats-toggle {{
            background: none;
            border: none;
            color: var(--text-secondary);
            font-size: 1.2em;
            cursor: pointer;
            transition: transform 0.3s;
        }}
        
        .bp-stats-toggle.collapsed {{
            transform: rotate(-90deg);
        }}
        
        .bp-stats-content {{
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 20px;
        }}
        
        .bp-stats-content.collapsed {{
            display: none;
        }}
        
        .bp-chart-container {{
            background: var(--bg-primary);
            border-radius: 12px;
            padding: 20px;
            border: 2px solid var(--border-color);
        }}
        
        .bp-chart-title {{
            font-size: 1em;
            color: var(--text-primary);
            margin-bottom: 15px;
            text-align: center;
            font-weight: 600;
        }}
        
        .bp-donut-container {{
            display: flex;
            justify-content: center;
            align-items: center;
            gap: 30px;
            flex-wrap: wrap;
        }}
        
        .bp-donut {{
            position: relative;
            width: 160px;
            height: 160px;
        }}
        
        .bp-donut svg {{
            width: 100%;
            height: 100%;
            transform: rotate(-90deg);
        }}
        
        .bp-donut-center {{
            position: absolute;
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            text-align: center;
        }}
        
        .bp-donut-value {{
            font-size: 1.8em;
            font-weight: bold;
            color: var(--match);
        }}
        
        .bp-donut-label {{
            font-size: 0.75em;
            color: var(--text-secondary);
            text-transform: uppercase;
        }}
        
        .bp-bar-chart {{
            display: flex;
            flex-direction: column;
            gap: 12px;
        }}
        
        .bp-bar-item {{
            display: flex;
            align-items: center;
            gap: 10px;
        }}
        
        .bp-bar-label {{
            width: 100px;
            font-size: 0.85em;
            color: var(--text-secondary);
            text-align: right;
        }}
        
        .bp-bar-container {{
            flex: 1;
            height: 24px;
            background: var(--bg-tertiary);
            border-radius: 12px;
            overflow: hidden;
            position: relative;
        }}
        
        .bp-bar {{
            height: 100%;
            border-radius: 12px;
            transition: width 0.5s ease;
            display: flex;
            align-items: center;
            justify-content: flex-end;
            padding-right: 8px;
        }}
        
        .bp-bar-value {{
            font-size: 0.75em;
            font-weight: bold;
            color: white;
            text-shadow: 1px 1px 2px rgba(0,0,0,0.5);
        }}
        
        .bp-bar.jal {{ background: linear-gradient(90deg, #00d26a, #00f2a0); }}
        .bp-bar.jalr {{ background: linear-gradient(90deg, #667eea, #764ba2); }}
        .bp-bar.cond {{ background: linear-gradient(90deg, #f093fb, #f5576c); }}
        .bp-bar.ras {{ background: linear-gradient(90deg, #4facfe, #00f2fe); }}
        
        .bp-stats-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(120px, 1fr));
            gap: 12px;
            margin-top: 15px;
        }}
        
        .bp-stat-card {{
            background: var(--bg-tertiary);
            padding: 12px;
            border-radius: 8px;
            text-align: center;
        }}
        
        .bp-stat-value {{
            font-size: 1.3em;
            font-weight: bold;
            color: var(--text-primary);
        }}
        
        .bp-stat-label {{
            font-size: 0.7em;
            color: var(--text-secondary);
            text-transform: uppercase;
            margin-top: 4px;
        }}
        
        @media (max-width: 768px) {{
            .bp-stats-content {{
                grid-template-columns: 1fr;
            }}
        }}
        
        /* Chart Container */
        .chart-container {{
            background: var(--bg-primary);
            border-radius: 8px;
            padding: 15px;
            border: 2px solid var(--border-color);
            display: flex;
            flex-direction: column;
            align-items: center;
        }}
        
        .chart-title {{
            font-size: 0.9em;
            color: var(--text-secondary);
            margin-bottom: 10px;
            text-transform: uppercase;
        }}
        
        .pie-chart {{
            width: 180px;
            height: 180px;
            border-radius: 50%;
            position: relative;
        }}
        
        .chart-legend {{
            display: flex;
            flex-wrap: wrap;
            gap: 8px;
            margin-top: 12px;
            justify-content: center;
        }}
        
        .legend-item {{
            display: flex;
            align-items: center;
            gap: 5px;
            font-size: 0.75em;
        }}
        
        .legend-dot {{
            width: 10px;
            height: 10px;
            border-radius: 50%;
        }}
        
        /* Controls */
        .controls {{
            padding: 15px 20px;
            background: var(--bg-secondary);
            border-bottom: 2px solid var(--border-color);
            display: flex;
            gap: 12px;
            flex-wrap: wrap;
            align-items: center;
        }}
        
        .search-box {{
            flex: 1;
            min-width: 200px;
            max-width: 400px;
            position: relative;
        }}
        
        .search-box input {{
            width: 100%;
            padding: 10px 15px 10px 40px;
            background: var(--bg-primary);
            border: 2px solid var(--border-color);
            border-radius: 6px;
            color: var(--text-primary);
            font-family: inherit;
            font-size: 0.9em;
        }}
        
        .search-box input:focus {{
            outline: none;
            border-color: var(--accent);
        }}
        
        .search-box::before {{
            content: "🔍";
            position: absolute;
            left: 12px;
            top: 50%;
            transform: translateY(-50%);
            font-size: 1em;
        }}
        
        .btn {{
            padding: 10px 18px;
            background: var(--accent);
            color: white;
            border: none;
            border-radius: 6px;
            cursor: pointer;
            font-size: 0.9em;
            transition: all 0.2s;
            font-family: inherit;
            white-space: nowrap;
        }}
        
        .btn:hover {{
            background: var(--accent-hover);
            transform: translateY(-1px);
        }}
        
        .btn-outline {{
            background: transparent;
            border: 2px solid var(--accent);
            color: var(--accent);
        }}
        
        .btn-outline:hover {{
            background: var(--accent);
            color: white;
        }}
        
        .btn-group {{
            display: flex;
            gap: 0;
        }}
        
        .btn-group .btn {{
            border-radius: 0;
        }}
        
        .btn-group .btn:first-child {{
            border-radius: 6px 0 0 6px;
        }}
        
        .btn-group .btn:last-child {{
            border-radius: 0 6px 6px 0;
        }}
        
        .btn-group .btn.active {{
            background: var(--accent-hover);
        }}
        
        select {{
            padding: 10px 15px;
            background: var(--bg-primary);
            border: 2px solid var(--border-color);
            border-radius: 6px;
            color: var(--text-primary);
            font-family: inherit;
            cursor: pointer;
        }}
        
        /* Error Navigation */
        .error-nav {{
            padding: 10px 20px;
            background: var(--bg-tertiary);
            display: flex;
            align-items: center;
            gap: 10px;
            flex-wrap: wrap;
        }}
        
        .error-nav-label {{
            color: var(--text-secondary);
            font-size: 0.85em;
        }}
        
        .error-btn {{
            padding: 5px 12px;
            background: var(--mismatch);
            color: white;
            border: none;
            border-radius: 4px;
            cursor: pointer;
            font-size: 0.8em;
            transition: all 0.2s;
        }}
        
        .error-btn:hover {{
            opacity: 0.8;
        }}
        
        /* Pagination */
        .pagination {{
            display: flex;
            align-items: center;
            gap: 10px;
            padding: 15px 20px;
            background: var(--bg-secondary);
            border-bottom: 2px solid var(--border-color);
            justify-content: space-between;
            flex-wrap: wrap;
        }}
        
        .page-info {{
            color: var(--text-secondary);
            font-size: 0.9em;
        }}
        
        .page-controls {{
            display: flex;
            align-items: center;
            gap: 8px;
        }}
        
        .page-btn {{
            padding: 8px 14px;
            background: var(--bg-primary);
            border: 2px solid var(--border-color);
            color: var(--text-primary);
            border-radius: 4px;
            cursor: pointer;
            transition: all 0.2s;
        }}
        
        .page-btn:hover:not(:disabled) {{
            border-color: var(--accent);
            background: var(--accent);
            color: white;
        }}
        
        .page-btn:disabled {{
            opacity: 0.5;
            cursor: not-allowed;
        }}
        
        .page-input {{
            width: 60px;
            padding: 8px;
            text-align: center;
            background: var(--bg-primary);
            border: 2px solid var(--border-color);
            color: var(--text-primary);
            border-radius: 4px;
        }}
        
        /* Table */
        .table-container {{
            overflow-x: auto;
            max-height: 70vh;
            overflow-y: auto;
        }}
        
        .diff-table {{
            width: 100%;
            border-collapse: collapse;
        }}
        
        .diff-table thead {{
            background: var(--bg-secondary);
            position: sticky;
            top: 0;
            z-index: 10;
        }}
        
        .diff-table th {{
            padding: 12px 10px;
            text-align: left;
            color: var(--info);
            font-weight: 600;
            border-bottom: 2px solid var(--accent);
            font-size: 0.9em;
            white-space: nowrap;
        }}
        
        .diff-table td {{
            padding: 10px;
            border-bottom: 1px solid var(--border-color);
            font-size: 0.85em;
            vertical-align: top;
        }}
        
        .cycle-num {{
            color: var(--text-secondary);
            font-weight: 600;
            width: 70px;
            text-align: center;
        }}
        
        .status-col {{
            width: 100px;
            text-align: center;
        }}
        
        .status-badge {{
            display: inline-block;
            padding: 4px 10px;
            border-radius: 12px;
            font-size: 0.8em;
            font-weight: 600;
        }}
        
        .status-match {{
            background: rgba(80, 250, 123, 0.15);
            color: var(--match);
            border: 1px solid var(--match);
        }}
        
        .status-mismatch {{
            background: rgba(255, 85, 85, 0.15);
            color: var(--mismatch);
            border: 1px solid var(--mismatch);
        }}
        
        .status-reg-warn {{
            background: rgba(241, 250, 140, 0.15);
            color: var(--warning);
            border: 1px solid var(--warning);
        }}
        
        .status-extra-rtl, .status-extra-spike {{
            background: rgba(139, 233, 253, 0.15);
            color: var(--info);
            border: 1px solid var(--info);
        }}
        
        .code-cell {{
            font-family: 'JetBrains Mono', monospace;
            white-space: nowrap;
        }}
        
        .pc {{ color: var(--pc-color); }}
        .inst {{ color: var(--inst-color); }}
        .reg {{ color: var(--reg-color); }}
        
        .highlight-diff {{
            background: rgba(255, 85, 85, 0.25);
            padding: 1px 3px;
            border-radius: 3px;
        }}
        
        .disasm-col {{
            color: var(--inst-color);
            font-size: 0.8em;
            max-width: 350px;
            overflow: hidden;
            text-overflow: ellipsis;
        }}
        
        tr:hover {{
            background: rgba(102, 126, 234, 0.08);
        }}
        
        tr.highlight-pass {{
            background: rgba(80, 250, 123, 0.2) !important;
        }}
        
        tr.highlight-fail {{
            background: rgba(255, 85, 85, 0.2) !important;
        }}
        
        tr.highlight-current {{
            background: rgba(102, 126, 234, 0.3) !important;
            outline: 2px solid var(--accent);
        }}
        
        /* Footer */
        footer {{
            padding: 20px;
            text-align: center;
            background: var(--bg-secondary);
            color: var(--text-secondary);
            font-size: 0.85em;
            border-top: 2px solid var(--border-color);
        }}
        
        .legend {{
            display: flex;
            gap: 20px;
            justify-content: center;
            flex-wrap: wrap;
            margin-bottom: 15px;
        }}
        
        .legend-item {{
            display: flex;
            align-items: center;
            gap: 6px;
        }}
        
        .legend-box {{
            width: 14px;
            height: 14px;
            border-radius: 3px;
        }}
        
        /* Keyboard shortcuts modal */
        .modal {{
            display: none;
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: rgba(0,0,0,0.7);
            z-index: 1000;
            justify-content: center;
            align-items: center;
        }}
        
        .modal.active {{
            display: flex;
        }}
        
        .modal-content {{
            background: var(--bg-primary);
            padding: 25px;
            border-radius: 12px;
            max-width: 500px;
            width: 90%;
            max-height: 80vh;
            overflow-y: auto;
        }}
        
        .modal-header {{
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 20px;
        }}
        
        .modal-header h2 {{
            color: var(--accent);
        }}
        
        .modal-close {{
            background: none;
            border: none;
            color: var(--text-secondary);
            font-size: 1.5em;
            cursor: pointer;
        }}
        
        .shortcut-list {{
            list-style: none;
        }}
        
        .shortcut-list li {{
            display: flex;
            justify-content: space-between;
            padding: 10px 0;
            border-bottom: 1px solid var(--border-color);
        }}
        
        .shortcut-key {{
            background: var(--bg-secondary);
            padding: 3px 8px;
            border-radius: 4px;
            font-family: monospace;
            border: 1px solid var(--border-color);
        }}
        
        /* Toast notifications */
        .toast {{
            position: fixed;
            bottom: 20px;
            right: 20px;
            background: var(--accent);
            color: white;
            padding: 12px 20px;
            border-radius: 8px;
            opacity: 0;
            transform: translateY(20px);
            transition: all 0.3s;
            z-index: 1001;
        }}
        
        .toast.show {{
            opacity: 1;
            transform: translateY(0);
        }}
        
        /* Loading overlay */
        .loading {{
            position: absolute;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: rgba(0,0,0,0.5);
            display: flex;
            justify-content: center;
            align-items: center;
            z-index: 100;
        }}
        
        .loading.hidden {{
            display: none;
        }}
        
        .spinner {{
            width: 40px;
            height: 40px;
            border: 4px solid var(--border-color);
            border-top-color: var(--accent);
            border-radius: 50%;
            animation: spin 1s linear infinite;
        }}
        
        @keyframes spin {{
            to {{ transform: rotate(360deg); }}
        }}
        
        /* Export dropdown */
        .dropdown {{
            position: relative;
            display: inline-block;
        }}
        
        .dropdown-content {{
            display: none;
            position: absolute;
            top: 100%;
            right: 0;
            background: var(--bg-primary);
            border: 2px solid var(--border-color);
            border-radius: 6px;
            min-width: 150px;
            z-index: 100;
            box-shadow: 0 4px 12px rgba(0,0,0,0.2);
        }}
        
        .dropdown:hover .dropdown-content {{
            display: block;
        }}
        
        .dropdown-item {{
            padding: 10px 15px;
            cursor: pointer;
            transition: background 0.2s;
            display: block;
            color: var(--text-primary);
            text-decoration: none;
        }}
        
        .dropdown-item:hover {{
            background: var(--bg-secondary);
        }}
        
        /* Responsive */
        @media (max-width: 1200px) {{
            .stats-section {{
                grid-template-columns: 1fr;
            }}
            
            .chart-container {{
                flex-direction: row;
                justify-content: center;
                gap: 20px;
            }}
        }}
        
        @media (max-width: 768px) {{
            .controls {{
                flex-direction: column;
                align-items: stretch;
            }}
            
            .search-box {{
                max-width: none;
            }}
            
            .btn-group {{
                justify-content: center;
            }}
            
            header h1 {{
                font-size: 1.5em;
            }}
            
            .theme-toggle {{
                position: static;
                margin-top: 10px;
            }}
        }}
    </style>
</head>
<body>
    <div class="container">
        <header>
            <button class="theme-toggle" onclick="toggleTheme()">🌓 Theme</button>
            <h1>🔬 CERES vs SPIKE</h1>
            <div class="subtitle">Commit Log Comparison Report</div>
            {test_info_html}
            <div class="subtitle" style="margin-top: 8px; font-size: 0.85em;">
                Generated: {timestamp}
            </div>
        </header>
        
        <!-- Stats Section with Chart -->
        <div class="stats-section">
            <div class="stats-container">
                <div class="stat-card">
                    <div class="stat-label">Total Cycles</div>
                    <div class="stat-value stat-info">{total_cycles:,}</div>
                </div>
                <div class="stat-card">
                    <div class="stat-label">✅ Matches</div>
                    <div class="stat-value stat-match">{stats['match']:,}</div>
                </div>
                <div class="stat-card">
                    <div class="stat-label">❌ PC/INST Mismatch</div>
                    <div class="stat-value stat-mismatch">{stats['pcinst_mismatch']:,}</div>
                </div>
                <div class="stat-card">
                    <div class="stat-label">⚠️ Reg Mismatch</div>
                    <div class="stat-value stat-warning">{stats['reg_mismatch']:,}</div>
                </div>
                <div class="stat-card">
                    <div class="stat-label">Match Rate</div>
                    <div class="stat-value {'stat-match' if match_rate > 90 else 'stat-warning' if match_rate > 50 else 'stat-mismatch'}">{match_rate:.1f}%</div>
                </div>
                <div class="stat-card">
                    <div class="stat-label">RTL Extra</div>
                    <div class="stat-value stat-info">{stats['insert_rtl']:,}</div>
                </div>
                <div class="stat-card">
                    <div class="stat-label">Spike Extra</div>
                    <div class="stat-value stat-info">{stats['insert_spike']:,}</div>
                </div>
                <div class="stat-card">
                    <div class="stat-label">🔄 Resyncs</div>
                    <div class="stat-value stat-info">{stats.get('resyncs', 0):,}</div>
                </div>
            </div>
            
            <!-- Pie Chart -->
            <div class="chart-container">
                <div class="chart-title">Result Distribution</div>
                <canvas id="pieChart" width="180" height="180"></canvas>
                <div class="chart-legend">
                    <div class="legend-item">
                        <div class="legend-dot" style="background: #50fa7b;"></div>
                        <span>Match</span>
                    </div>
                    <div class="legend-item">
                        <div class="legend-dot" style="background: #ff5555;"></div>
                        <span>Mismatch</span>
                    </div>
                    <div class="legend-item">
                        <div class="legend-dot" style="background: #f1fa8c;"></div>
                        <span>Reg Warn</span>
                    </div>
                    <div class="legend-item">
                        <div class="legend-dot" style="background: #8be9fd;"></div>
                        <span>Extra</span>
                    </div>
                </div>
            </div>
        </div>
        
        <!-- Branch Predictor Stats Section -->
        <div class="bp-stats-section" id="bpStatsSection" style="display: none;">
            <div class="bp-stats-header" onclick="toggleBpStats()">
                <button class="bp-stats-toggle" id="bpToggle">▼</button>
                <h3>🎯 Branch Predictor Statistics</h3>
            </div>
            <div class="bp-stats-content" id="bpStatsContent">
                <div class="bp-chart-container">
                    <div class="bp-chart-title">Overall Prediction Accuracy</div>
                    <div class="bp-donut-container">
                        <div class="bp-donut">
                            <svg viewBox="0 0 36 36">
                                <circle cx="18" cy="18" r="15.9" fill="none" stroke="var(--bg-tertiary)" stroke-width="3"></circle>
                                <circle id="bpAccuracyCircle" cx="18" cy="18" r="15.9" fill="none" stroke="var(--match)" stroke-width="3" stroke-dasharray="0, 100" stroke-linecap="round"></circle>
                            </svg>
                            <div class="bp-donut-center">
                                <div class="bp-donut-value" id="bpAccuracyValue">--%</div>
                                <div class="bp-donut-label">Accuracy</div>
                            </div>
                        </div>
                        <div class="bp-stats-grid" id="bpOverviewStats">
                            <!-- Filled by JS -->
                        </div>
                    </div>
                </div>
                <div class="bp-chart-container">
                    <div class="bp-chart-title">Branch Type Breakdown</div>
                    <div class="bp-bar-chart" id="bpBarChart">
                        <!-- Filled by JS -->
                    </div>
                </div>
            </div>
        </div>
        
        <!-- Controls -->
        <div class="controls">
            <div class="search-box">
                <input type="text" id="searchInput" placeholder="Search PC, instruction, register..." onkeyup="handleSearch(event)">
            </div>
            
            <div class="btn-group">
                <button class="btn active" onclick="setFilter('all', this)">All</button>
                <button class="btn" onclick="setFilter('mismatch', this)">Errors</button>
                <button class="btn" onclick="setFilter('match', this)">Match</button>
            </div>
            
            <select id="pageSize" onchange="changePageSize()">
                <option value="50">50 per page</option>
                <option value="100" selected>100 per page</option>
                <option value="250">250 per page</option>
                <option value="500">500 per page</option>
                <option value="all">Show all</option>
            </select>
            
            <div class="dropdown">
                <button class="btn btn-outline">📥 Export</button>
                <div class="dropdown-content">
                    <a class="dropdown-item" onclick="exportCSV()">📄 Export CSV</a>
                    <a class="dropdown-item" onclick="exportJSON()">📋 Export JSON</a>
                    <a class="dropdown-item" onclick="exportFilteredCSV()">📄 Export Filtered CSV</a>
                </div>
            </div>
            
            <button class="btn btn-outline" onclick="showShortcuts()">⌨️ Shortcuts</button>
        </div>
        
        <!-- Error Navigation -->
        <div class="error-nav" id="errorNav" style="{'display:none;' if len(error_indices) == 0 else ''}">
            <span class="error-nav-label">Quick jump to errors ({len(error_indices)} found):</span>
            <button class="error-btn" onclick="jumpToError(0)">1st</button>
            <button class="error-btn" onclick="jumpToError(1)">2nd</button>
            <button class="error-btn" onclick="jumpToError(2)">3rd</button>
            <button class="error-btn" onclick="jumpToError(4)">5th</button>
            <button class="error-btn" onclick="jumpToError(9)">10th</button>
            <button class="error-btn" onclick="prevError()">◀ Prev</button>
            <button class="error-btn" onclick="nextError()">Next ▶</button>
            <span class="error-nav-label" id="errorPosition"></span>
        </div>
        
        <!-- Pagination -->
        <div class="pagination">
            <div class="page-info">
                Showing <span id="showingFrom">1</span>-<span id="showingTo">100</span> of <span id="totalFiltered">{total_cycles:,}</span> entries
            </div>
            <div class="page-controls">
                <button class="page-btn" onclick="firstPage()">⏮</button>
                <button class="page-btn" onclick="prevPage()">◀</button>
                <span>Page</span>
                <input type="number" class="page-input" id="pageInput" value="1" min="1" onchange="goToPage()">
                <span>of <span id="totalPages">1</span></span>
                <button class="page-btn" onclick="nextPage()">▶</button>
                <button class="page-btn" onclick="lastPage()">⏭</button>
            </div>
        </div>
        
        <!-- Table -->
        <div class="table-container" style="position: relative;">
            <div class="loading hidden" id="loading">
                <div class="spinner"></div>
            </div>
            <table class="diff-table" id="diffTable">
                <thead>
                    <tr>
                        <th>#</th>
                        <th>Status</th>
                        <th>CERES (RTL)</th>
                        <th>SPIKE (Golden)</th>
                        {'<th>Disassembly</th>' if disasm_map else ''}
                    </tr>
                </thead>
                <tbody id="tableBody">
                    <!-- Rows will be inserted by JavaScript -->
                </tbody>
            </table>
        </div>
        
        <!-- Footer -->
        <footer>
            <div class="legend">
                <div class="legend-item">
                    <div class="legend-box" style="background: rgba(80, 250, 123, 0.3); border: 1px solid #50fa7b;"></div>
                    <span>Perfect Match</span>
                </div>
                <div class="legend-item">
                    <div class="legend-box" style="background: rgba(255, 85, 85, 0.3); border: 1px solid #ff5555;"></div>
                    <span>PC/INST Mismatch</span>
                </div>
                <div class="legend-item">
                    <div class="legend-box" style="background: rgba(241, 250, 140, 0.3); border: 1px solid #f1fa8c;"></div>
                    <span>Register Mismatch</span>
                </div>
                <div class="legend-item">
                    <div class="legend-box" style="background: rgba(139, 233, 253, 0.3); border: 1px solid #8be9fd;"></div>
                    <span>Extra Entry</span>
                </div>
            </div>
            <div>CERES RISC-V Processor Verification Suite | Press <kbd>?</kbd> for keyboard shortcuts</div>
        </footer>
    </div>
    
    <!-- Keyboard Shortcuts Modal -->
    <div class="modal" id="shortcutsModal">
        <div class="modal-content">
            <div class="modal-header">
                <h2>⌨️ Keyboard Shortcuts</h2>
                <button class="modal-close" onclick="hideShortcuts()">&times;</button>
            </div>
            <ul class="shortcut-list">
                <li><span>Show this help</span><span class="shortcut-key">?</span></li>
                <li><span>Search</span><span class="shortcut-key">/</span></li>
                <li><span>Next page</span><span class="shortcut-key">→</span></li>
                <li><span>Previous page</span><span class="shortcut-key">←</span></li>
                <li><span>First page</span><span class="shortcut-key">Home</span></li>
                <li><span>Last page</span><span class="shortcut-key">End</span></li>
                <li><span>Next error</span><span class="shortcut-key">n</span></li>
                <li><span>Previous error</span><span class="shortcut-key">p</span></li>
                <li><span>Toggle theme</span><span class="shortcut-key">t</span></li>
                <li><span>Filter: All</span><span class="shortcut-key">a</span></li>
                <li><span>Filter: Errors only</span><span class="shortcut-key">e</span></li>
                <li><span>Filter: Matches only</span><span class="shortcut-key">m</span></li>
                <li><span>Export CSV</span><span class="shortcut-key">Ctrl+S</span></li>
                <li><span>Close modal</span><span class="shortcut-key">Esc</span></li>
            </ul>
        </div>
    </div>
    
    <!-- Toast -->
    <div class="toast" id="toast"></div>
    
    <script>
        // Data
        const allRows = {rows_json};
        const stats = {stats_json};
        const errorIndices = {error_indices_json};
        const hasDisasm = {'true' if disasm_map else 'false'};
        const bpStats = {bp_stats_json};
        
        // State
        let filteredRows = [...allRows];
        let currentPage = 1;
        let pageSize = 100;
        let currentFilter = 'all';
        let searchQuery = '';
        let currentErrorIdx = -1;
        
        // Initialize
        document.addEventListener('DOMContentLoaded', () => {{
            renderTable();
            drawPieChart();
            setupKeyboardShortcuts();
            renderBpStats();
            
            // Auto-scroll to first error if exists
            if (errorIndices.length > 0) {{
                setTimeout(() => jumpToError(0), 500);
            }}
        }});
        
        // Render Branch Predictor Stats
        function renderBpStats() {{
            if (!bpStats || bpStats.total_branches === 0) {{
                return;
            }}
            
            // Show the BP stats section
            document.getElementById('bpStatsSection').style.display = 'block';
            
            // Update accuracy donut
            const accuracy = bpStats.accuracy || 0;
            const circle = document.getElementById('bpAccuracyCircle');
            circle.setAttribute('stroke-dasharray', `${{accuracy}}, 100`);
            circle.setAttribute('stroke', accuracy >= 90 ? 'var(--match)' : accuracy >= 70 ? 'var(--warning)' : 'var(--mismatch)');
            document.getElementById('bpAccuracyValue').textContent = accuracy.toFixed(1) + '%';
            document.getElementById('bpAccuracyValue').style.color = 
                accuracy >= 90 ? 'var(--match)' : accuracy >= 70 ? 'var(--warning)' : 'var(--mismatch)';
            
            // Overview stats grid
            const overviewHtml = `
                <div class="bp-stat-card">
                    <div class="bp-stat-value">${{bpStats.total_branches.toLocaleString()}}</div>
                    <div class="bp-stat-label">Total Branches</div>
                </div>
                <div class="bp-stat-card">
                    <div class="bp-stat-value" style="color: var(--match);">${{bpStats.correct.toLocaleString()}}</div>
                    <div class="bp-stat-label">Correct</div>
                </div>
                <div class="bp-stat-card">
                    <div class="bp-stat-value" style="color: var(--mismatch);">${{bpStats.mispred.toLocaleString()}}</div>
                    <div class="bp-stat-label">Mispredicted</div>
                </div>
            `;
            document.getElementById('bpOverviewStats').innerHTML = overviewHtml;
            
            // Bar chart for branch types
            const barData = [
                {{ label: 'JAL (Direct)', total: bpStats.jal_total, correct: bpStats.jal_correct, accuracy: bpStats.jal_accuracy, class: 'jal' }},
                {{ label: 'JALR (Indirect)', total: bpStats.jalr_total, correct: bpStats.jalr_correct, accuracy: bpStats.jalr_accuracy, class: 'jalr' }},
                {{ label: 'Conditional', total: bpStats.cond_total, correct: bpStats.cond_correct, accuracy: bpStats.cond_accuracy, class: 'cond' }},
                {{ label: 'RAS', total: bpStats.ras_total, correct: bpStats.ras_correct, accuracy: bpStats.ras_accuracy, class: 'ras' }}
            ];
            
            let barHtml = '';
            barData.forEach(item => {{
                if (item.total > 0) {{
                    const pct = item.accuracy || 0;
                    barHtml += `
                        <div class="bp-bar-item">
                            <div class="bp-bar-label">${{item.label}}</div>
                            <div class="bp-bar-container">
                                <div class="bp-bar ${{item.class}}" style="width: ${{Math.max(pct, 5)}}%;">
                                    <span class="bp-bar-value">${{pct.toFixed(1)}}%</span>
                                </div>
                            </div>
                            <div style="width: 80px; font-size: 0.75em; color: var(--text-secondary);">
                                ${{item.correct}}/${{item.total}}
                            </div>
                        </div>
                    `;
                }}
            }});
            
            if (barHtml === '') {{
                barHtml = '<div style="text-align: center; color: var(--text-secondary); padding: 20px;">No branch type data available</div>';
            }}
            
            document.getElementById('bpBarChart').innerHTML = barHtml;
        }}
        
        // Toggle BP Stats Section
        function toggleBpStats() {{
            const content = document.getElementById('bpStatsContent');
            const toggle = document.getElementById('bpToggle');
            content.classList.toggle('collapsed');
            toggle.classList.toggle('collapsed');
        }}
        
        // Render table
        function renderTable() {{
            const tbody = document.getElementById('tableBody');
            const start = (currentPage - 1) * pageSize;
            const end = pageSize === 'all' ? filteredRows.length : Math.min(start + pageSize, filteredRows.length);
            const pageRows = filteredRows.slice(start, end);
            
            let html = '';
            pageRows.forEach(row => {{
                const statusMap = {{
                    'match': ['status-match', '✅ MATCH'],
                    'mismatch': ['status-mismatch', '❌ DIFF'],
                    'reg-warn': ['status-reg-warn', '⚠️ REG'],
                    'extra-rtl': ['status-extra-rtl', '➕ RTL'],
                    'extra-spike': ['status-extra-spike', '➕ SPIKE']
                }};
                
                const [statusClass, statusText] = statusMap[row.status] || ['', row.status];
                const highlightClass = row.highlight === 'pass' ? 'highlight-pass' : row.highlight === 'fail' ? 'highlight-fail' : '';
                
                let rtlHtml = '—';
                let spikeHtml = '—';
                
                if (row.rtl) {{
                    let pcHtml = `<span class="pc">PC=${{row.rtl.pc}}</span>`;
                    let instHtml = `<span class="inst">INST=${{row.rtl.inst}}</span>`;
                    
                    // Highlight differences
                    if (row.spike && row.status === 'mismatch') {{
                        if (row.rtl.pc !== row.spike.pc) {{
                            pcHtml = `<span class="pc highlight-diff">PC=${{row.rtl.pc}}</span>`;
                        }}
                        if (row.rtl.inst !== row.spike.inst) {{
                            instHtml = `<span class="inst highlight-diff">INST=${{row.rtl.inst}}</span>`;
                        }}
                    }}
                    
                    rtlHtml = `${{pcHtml}} ${{instHtml}} <span class="reg">${{row.rtl.reg}}</span>`;
                }}
                
                if (row.spike) {{
                    let pcHtml = `<span class="pc">PC=${{row.spike.pc}}</span>`;
                    let instHtml = `<span class="inst">INST=${{row.spike.inst}}</span>`;
                    
                    if (row.rtl && row.status === 'mismatch') {{
                        if (row.rtl.pc !== row.spike.pc) {{
                            pcHtml = `<span class="pc highlight-diff">PC=${{row.spike.pc}}</span>`;
                        }}
                        if (row.rtl.inst !== row.spike.inst) {{
                            instHtml = `<span class="inst highlight-diff">INST=${{row.spike.inst}}</span>`;
                        }}
                    }}
                    
                    spikeHtml = `${{pcHtml}} ${{instHtml}} <span class="reg">${{row.spike.reg}}</span>`;
                }}
                
                const disasmCell = hasDisasm ? `<td class="disasm-col">${{row.disasm || '—'}}</td>` : '';
                
                html += `
                    <tr class="${{highlightClass}}" data-idx="${{row.idx}}" id="row${{row.idx}}">
                        <td class="cycle-num">${{row.idx + 1}}</td>
                        <td class="status-col"><span class="status-badge ${{statusClass}}">${{statusText}}</span></td>
                        <td class="code-cell">${{rtlHtml}}</td>
                        <td class="code-cell">${{spikeHtml}}</td>
                        ${{disasmCell}}
                    </tr>
                `;
            }});
            
            tbody.innerHTML = html;
            updatePaginationInfo();
        }}
        
        // Filter rows
        function applyFilters() {{
            filteredRows = allRows.filter(row => {{
                // Apply status filter
                if (currentFilter === 'mismatch' && row.status === 'match') return false;
                if (currentFilter === 'match' && row.status !== 'match') return false;
                
                // Apply search
                if (searchQuery) {{
                    const q = searchQuery.toLowerCase();
                    const rtlMatch = row.rtl && (
                        row.rtl.pc.toLowerCase().includes(q) ||
                        row.rtl.inst.toLowerCase().includes(q) ||
                        row.rtl.reg.toLowerCase().includes(q)
                    );
                    const spikeMatch = row.spike && (
                        row.spike.pc.toLowerCase().includes(q) ||
                        row.spike.inst.toLowerCase().includes(q) ||
                        row.spike.reg.toLowerCase().includes(q)
                    );
                    const disasmMatch = row.disasm && row.disasm.toLowerCase().includes(q);
                    
                    if (!rtlMatch && !spikeMatch && !disasmMatch) return false;
                }}
                
                return true;
            }});
            
            currentPage = 1;
            renderTable();
        }}
        
        function setFilter(filter, btn) {{
            currentFilter = filter;
            document.querySelectorAll('.btn-group .btn').forEach(b => b.classList.remove('active'));
            btn.classList.add('active');
            applyFilters();
        }}
        
        function handleSearch(event) {{
            searchQuery = event.target.value;
            applyFilters();
        }}
        
        // Pagination
        function updatePaginationInfo() {{
            const total = filteredRows.length;
            const size = pageSize === 'all' ? total : pageSize;
            const start = (currentPage - 1) * size + 1;
            const end = Math.min(currentPage * size, total);
            const totalPages = Math.ceil(total / size) || 1;
            
            document.getElementById('showingFrom').textContent = total > 0 ? start : 0;
            document.getElementById('showingTo').textContent = end;
            document.getElementById('totalFiltered').textContent = total.toLocaleString();
            document.getElementById('totalPages').textContent = totalPages;
            document.getElementById('pageInput').value = currentPage;
            document.getElementById('pageInput').max = totalPages;
        }}
        
        function changePageSize() {{
            const val = document.getElementById('pageSize').value;
            pageSize = val === 'all' ? 'all' : parseInt(val);
            currentPage = 1;
            renderTable();
        }}
        
        function prevPage() {{
            if (currentPage > 1) {{
                currentPage--;
                renderTable();
            }}
        }}
        
        function nextPage() {{
            const totalPages = Math.ceil(filteredRows.length / (pageSize === 'all' ? filteredRows.length : pageSize));
            if (currentPage < totalPages) {{
                currentPage++;
                renderTable();
            }}
        }}
        
        function firstPage() {{
            currentPage = 1;
            renderTable();
        }}
        
        function lastPage() {{
            const totalPages = Math.ceil(filteredRows.length / (pageSize === 'all' ? filteredRows.length : pageSize));
            currentPage = totalPages;
            renderTable();
        }}
        
        function goToPage() {{
            const page = parseInt(document.getElementById('pageInput').value);
            const totalPages = Math.ceil(filteredRows.length / (pageSize === 'all' ? filteredRows.length : pageSize));
            if (page >= 1 && page <= totalPages) {{
                currentPage = page;
                renderTable();
            }}
        }}
        
        // Error navigation
        function jumpToError(errorNum) {{
            if (errorNum >= errorIndices.length) {{
                showToast('No more errors');
                return;
            }}
            
            currentErrorIdx = errorNum;
            const rowIdx = errorIndices[errorNum];
            
            // Find which page this row is on
            const rowInFiltered = filteredRows.findIndex(r => r.idx === rowIdx);
            if (rowInFiltered === -1) {{
                // Need to show all or reset filter
                currentFilter = 'all';
                document.querySelectorAll('.btn-group .btn').forEach(b => b.classList.remove('active'));
                document.querySelector('.btn-group .btn').classList.add('active');
                applyFilters();
            }}
            
            const size = pageSize === 'all' ? filteredRows.length : pageSize;
            currentPage = Math.floor(rowInFiltered / size) + 1;
            renderTable();
            
            setTimeout(() => {{
                const row = document.getElementById(`row${{rowIdx}}`);
                if (row) {{
                    row.scrollIntoView({{ behavior: 'smooth', block: 'center' }});
                    row.classList.add('highlight-current');
                    setTimeout(() => row.classList.remove('highlight-current'), 2000);
                }}
            }}, 100);
            
            updateErrorPosition();
        }}
        
        function prevError() {{
            if (currentErrorIdx > 0) {{
                jumpToError(currentErrorIdx - 1);
            }}
        }}
        
        function nextError() {{
            if (currentErrorIdx < errorIndices.length - 1) {{
                jumpToError(currentErrorIdx + 1);
            }}
        }}
        
        function updateErrorPosition() {{
            document.getElementById('errorPosition').textContent = 
                `(${{currentErrorIdx + 1}} of ${{errorIndices.length}})`;
        }}
        
        // Pie Chart
        function drawPieChart() {{
            const canvas = document.getElementById('pieChart');
            const ctx = canvas.getContext('2d');
            const centerX = canvas.width / 2;
            const centerY = canvas.height / 2;
            const radius = 80;
            
            const data = [
                {{ value: stats.match, color: '#50fa7b' }},
                {{ value: stats.pcinst_mismatch, color: '#ff5555' }},
                {{ value: stats.reg_mismatch, color: '#f1fa8c' }},
                {{ value: stats.insert_rtl + stats.insert_spike, color: '#8be9fd' }}
            ];
            
            const total = data.reduce((sum, d) => sum + d.value, 0);
            if (total === 0) return;
            
            let startAngle = -Math.PI / 2;
            
            data.forEach(segment => {{
                if (segment.value === 0) return;
                
                const sliceAngle = (segment.value / total) * 2 * Math.PI;
                
                ctx.beginPath();
                ctx.moveTo(centerX, centerY);
                ctx.arc(centerX, centerY, radius, startAngle, startAngle + sliceAngle);
                ctx.closePath();
                ctx.fillStyle = segment.color;
                ctx.fill();
                
                startAngle += sliceAngle;
            }});
            
            // Center circle for donut effect
            ctx.beginPath();
            ctx.arc(centerX, centerY, radius * 0.5, 0, 2 * Math.PI);
            ctx.fillStyle = getComputedStyle(document.body).getPropertyValue('--bg-primary').trim() || '#1e1e2e';
            ctx.fill();
            
            // Center text
            ctx.fillStyle = getComputedStyle(document.body).getPropertyValue('--text-primary').trim() || '#e0e0e0';
            ctx.font = 'bold 16px JetBrains Mono';
            ctx.textAlign = 'center';
            ctx.textBaseline = 'middle';
            const matchRate = ((stats.match / total) * 100).toFixed(1);
            ctx.fillText(`${{matchRate}}%`, centerX, centerY);
        }}
        
        // Theme
        function toggleTheme() {{
            const html = document.documentElement;
            const current = html.getAttribute('data-theme');
            const newTheme = current === 'light' ? 'dark' : 'light';
            html.setAttribute('data-theme', newTheme);
            localStorage.setItem('theme', newTheme);
            
            // Redraw chart with new colors
            setTimeout(drawPieChart, 100);
            
            showToast(`Switched to ${{newTheme}} theme`);
        }}
        
        // Load saved theme
        const savedTheme = localStorage.getItem('theme');
        if (savedTheme) {{
            document.documentElement.setAttribute('data-theme', savedTheme);
        }}
        
        // Export functions
        function exportCSV() {{
            let csv = 'Cycle,Status,RTL_PC,RTL_INST,RTL_REG,SPIKE_PC,SPIKE_INST,SPIKE_REG,Disasm\\n';
            
            allRows.forEach(row => {{
                csv += `${{row.idx + 1}},${{row.status}},`;
                csv += row.rtl ? `${{row.rtl.pc}},${{row.rtl.inst}},"${{row.rtl.reg}}"` : ',,,';
                csv += ',';
                csv += row.spike ? `${{row.spike.pc}},${{row.spike.inst}},"${{row.spike.reg}}"` : ',,,';
                csv += `,"${{row.disasm}}"\\n`;
            }});
            
            downloadFile(csv, 'comparison_report.csv', 'text/csv');
            showToast('CSV exported successfully');
        }}
        
        function exportFilteredCSV() {{
            let csv = 'Cycle,Status,RTL_PC,RTL_INST,RTL_REG,SPIKE_PC,SPIKE_INST,SPIKE_REG,Disasm\\n';
            
            filteredRows.forEach(row => {{
                csv += `${{row.idx + 1}},${{row.status}},`;
                csv += row.rtl ? `${{row.rtl.pc}},${{row.rtl.inst}},"${{row.rtl.reg}}"` : ',,,';
                csv += ',';
                csv += row.spike ? `${{row.spike.pc}},${{row.spike.inst}},"${{row.spike.reg}}"` : ',,,';
                csv += `,"${{row.disasm}}"\\n`;
            }});
            
            downloadFile(csv, 'comparison_filtered.csv', 'text/csv');
            showToast('Filtered CSV exported');
        }}
        
        function exportJSON() {{
            const data = {{
                stats: stats,
                rows: allRows,
                generated: '{timestamp}',
                test: '{test_name or ""}'
            }};
            
            downloadFile(JSON.stringify(data, null, 2), 'comparison_report.json', 'application/json');
            showToast('JSON exported successfully');
        }}
        
        function downloadFile(content, filename, type) {{
            const blob = new Blob([content], {{ type }});
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = filename;
            a.click();
            URL.revokeObjectURL(url);
        }}
        
        // Toast
        function showToast(message) {{
            const toast = document.getElementById('toast');
            toast.textContent = message;
            toast.classList.add('show');
            setTimeout(() => toast.classList.remove('show'), 3000);
        }}
        
        // Modal
        function showShortcuts() {{
            document.getElementById('shortcutsModal').classList.add('active');
        }}
        
        function hideShortcuts() {{
            document.getElementById('shortcutsModal').classList.remove('active');
        }}
        
        // Keyboard shortcuts
        function setupKeyboardShortcuts() {{
            document.addEventListener('keydown', (e) => {{
                // Ignore if typing in input
                if (e.target.tagName === 'INPUT') {{
                    if (e.key === 'Escape') {{
                        e.target.blur();
                    }}
                    return;
                }}
                
                switch(e.key) {{
                    case '?':
                        showShortcuts();
                        break;
                    case '/':
                        e.preventDefault();
                        document.getElementById('searchInput').focus();
                        break;
                    case 'ArrowRight':
                        nextPage();
                        break;
                    case 'ArrowLeft':
                        prevPage();
                        break;
                    case 'Home':
                        firstPage();
                        break;
                    case 'End':
                        lastPage();
                        break;
                    case 'n':
                        nextError();
                        break;
                    case 'p':
                        prevError();
                        break;
                    case 't':
                        toggleTheme();
                        break;
                    case 'a':
                        setFilter('all', document.querySelector('.btn-group .btn:first-child'));
                        break;
                    case 'e':
                        setFilter('mismatch', document.querySelector('.btn-group .btn:nth-child(2)'));
                        break;
                    case 'm':
                        setFilter('match', document.querySelector('.btn-group .btn:last-child'));
                        break;
                    case 'Escape':
                        hideShortcuts();
                        break;
                }}
                
                if (e.ctrlKey && e.key === 's') {{
                    e.preventDefault();
                    exportCSV();
                }}
            }});
        }}
    </script>
</body>
</html>
"""
    
    with open(html_path, "w") as f:
        f.write(html_content)
    
    # Try to get QUIET from compare_logs module
    try:
        from compare_logs import QUIET as quiet_mode
    except ImportError:
        quiet_mode = False
    
    if not quiet_mode:
        print(f"{Fore.CYAN}🌐 Enhanced HTML diff written to {html_path}{Style.RESET_ALL}")