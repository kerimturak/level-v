#!/usr/bin/env python3
"""
html_diff_generator.py — Beautiful HTML Report Generator for CERES vs SPIKE
============================================================================
Generates interactive, color-coded HTML comparison reports.
"""
from datetime import datetime
from colorama import Fore, Style

def entries_equal(a, b):
    """Check if two log entries have matching PC and INST"""
    return a[0] == b[0] and a[1] == b[1]


def generate_html_diff(rtl, spike, html_path, stats, disasm_map=None, 
                      pass_addr=None, fail_addr=None, test_name=None):
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
    """
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    
    # Calculate detailed statistics
    total_cycles = max(len(rtl), len(spike))
    match_rate = (stats["match"] / total_cycles * 100) if total_cycles > 0 else 0
    
    # Build test info section
    test_info_html = ""
    if test_name:
        test_info_html += f'<div class="subtitle" style="margin-top: 15px; font-size: 1em; color: #8be9fd;">Test: <strong>{test_name}</strong></div>'
    if pass_addr is not None:
        test_info_html += f'<div class="subtitle" style="font-size: 0.95em; color: #50fa7b;">✅ Pass Address: <strong>0x{pass_addr:08x}</strong></div>'
    if fail_addr is not None:
        test_info_html += f'<div class="subtitle" style="font-size: 0.95em; color: #ff5555;">❌ Fail Address: <strong>0x{fail_addr:08x}</strong></div>'
    
    html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>CERES vs SPIKE - {test_name or 'Commit Log Comparison'}</title>
    <style>
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}
        
        body {{
            font-family: 'JetBrains Mono', 'Fira Code', 'Consolas', monospace;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: #e0e0e0;
            padding: 20px;
            line-height: 1.6;
        }}
        
        .container {{
            max-width: 1800px;
            margin: 0 auto;
            background: #1e1e2e;
            border-radius: 12px;
            box-shadow: 0 8px 32px rgba(0, 0, 0, 0.3);
            overflow: hidden;
        }}
        
        header {{
            background: linear-gradient(135deg, #434343 0%, #000000 100%);
            padding: 30px;
            text-align: center;
            border-bottom: 3px solid #667eea;
        }}
        
        header h1 {{
            font-size: 2.5em;
            color: #fff;
            text-shadow: 2px 2px 4px rgba(0,0,0,0.5);
            margin-bottom: 10px;
        }}
        
        .subtitle {{
            color: #a0a0a0;
            font-size: 1.1em;
        }}
        
        .stats-container {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 15px;
            padding: 25px;
            background: #2a2a3e;
            border-bottom: 2px solid #3a3a4e;
        }}
        
        .stat-card {{
            background: #1e1e2e;
            padding: 20px;
            border-radius: 8px;
            text-align: center;
            border: 2px solid #3a3a4e;
            transition: transform 0.2s, border-color 0.2s;
        }}
        
        .stat-card:hover {{
            transform: translateY(-3px);
            border-color: #667eea;
        }}
        
        .stat-label {{
            color: #a0a0a0;
            font-size: 0.9em;
            text-transform: uppercase;
            letter-spacing: 1px;
            margin-bottom: 8px;
        }}
        
        .stat-value {{
            font-size: 2em;
            font-weight: bold;
        }}
        
        .stat-match {{ color: #50fa7b; }}
        .stat-mismatch {{ color: #ff5555; }}
        .stat-warning {{ color: #f1fa8c; }}
        .stat-info {{ color: #8be9fd; }}
        
        .controls {{
            padding: 20px 25px;
            background: #2a2a3e;
            border-bottom: 2px solid #3a3a4e;
            display: flex;
            gap: 15px;
            flex-wrap: wrap;
            align-items: center;
        }}
        
        .btn {{
            padding: 10px 20px;
            background: #667eea;
            color: white;
            border: none;
            border-radius: 6px;
            cursor: pointer;
            font-size: 0.95em;
            transition: all 0.2s;
            font-family: inherit;
        }}
        
        .btn:hover {{
            background: #5568d3;
            transform: translateY(-2px);
            box-shadow: 0 4px 12px rgba(102, 126, 234, 0.4);
        }}
        
        .filter-group {{
            display: flex;
            gap: 10px;
            align-items: center;
        }}
        
        .filter-group label {{
            color: #a0a0a0;
            font-size: 0.9em;
        }}
        
        .diff-table {{
            width: 100%;
            border-collapse: collapse;
        }}
        
        .diff-table thead {{
            background: #2a2a3e;
            position: sticky;
            top: 0;
            z-index: 10;
        }}
        
        .diff-table th {{
            padding: 15px 10px;
            text-align: left;
            color: #8be9fd;
            font-weight: 600;
            border-bottom: 2px solid #667eea;
            font-size: 0.95em;
        }}
        
        .diff-table td {{
            padding: 12px 10px;
            border-bottom: 1px solid #3a3a4e;
            font-size: 0.9em;
        }}
        
        .cycle-num {{
            color: #6272a4;
            font-weight: 600;
            width: 60px;
        }}
        
        .status-col {{
            width: 100px;
            text-align: center;
        }}
        
        .status-badge {{
            display: inline-block;
            padding: 4px 12px;
            border-radius: 12px;
            font-size: 0.85em;
            font-weight: 600;
        }}
        
        .match {{
            background: rgba(80, 250, 123, 0.15);
            color: #50fa7b;
            border: 1px solid #50fa7b;
        }}
        
        .mismatch {{
            background: rgba(255, 85, 85, 0.15);
            color: #ff5555;
            border: 1px solid #ff5555;
        }}
        
        .reg-warn {{
            background: rgba(241, 250, 140, 0.15);
            color: #f1fa8c;
            border: 1px solid #f1fa8c;
        }}
        
        .extra {{
            background: rgba(139, 233, 253, 0.15);
            color: #8be9fd;
            border: 1px solid #8be9fd;
        }}
        
        .code-cell {{
            font-family: 'JetBrains Mono', monospace;
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
            max-width: 600px;
        }}
        
        .pc {{ color: #ff79c6; }}
        .inst {{ color: #bd93f9; }}
        .reg {{ color: #8be9fd; }}
        
        .highlight-diff {{
            background: rgba(255, 85, 85, 0.2);
            padding: 2px 4px;
            border-radius: 3px;
        }}
        
        tr:hover {{
            background: rgba(102, 126, 234, 0.1);
        }}
        
        footer {{
            padding: 20px;
            text-align: center;
            background: #2a2a3e;
            color: #6272a4;
            font-size: 0.9em;
            border-top: 2px solid #3a3a4e;
        }}
        
        .legend {{
            display: flex;
            gap: 20px;
            justify-content: center;
            flex-wrap: wrap;
            margin-top: 10px;
        }}
        
        .legend-item {{
            display: flex;
            align-items: center;
            gap: 8px;
        }}
        
        .legend-box {{
            width: 16px;
            height: 16px;
            border-radius: 3px;
        }}
        
        .disasm-col {{
            font-family: 'JetBrains Mono', monospace;
            font-size: 0.85em;
            color: #bd93f9;
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
            max-width: 400px;
        }}
        
        .pass-addr-highlight {{
            background: rgba(80, 250, 123, 0.3) !important;
            border: 2px solid #50fa7b !important;
        }}
        
        .fail-addr-highlight {{
            background: rgba(255, 85, 85, 0.3) !important;
            border: 2px solid #ff5555 !important;
        }}
        
        @media (max-width: 768px) {{
            .stats-container {{
                grid-template-columns: 1fr;
            }}
            
            .code-cell {{
                max-width: 200px;
            }}
            
            .disasm-col {{
                max-width: 150px;
            }}
        }}
    </style>
</head>
<body>
    <div class="container">
        <header>
            <h1>🔬 CERES vs SPIKE</h1>
            <div class="subtitle">Commit Log Comparison Report</div>
            {test_info_html}
            <div class="subtitle" style="margin-top: 10px; font-size: 0.9em;">
                Generated: {timestamp}
            </div>
        </header>
        
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
                <div class="stat-label">❌ PC/INST Mismatches</div>
                <div class="stat-value stat-mismatch">{stats['pcinst_mismatch']:,}</div>
            </div>
            <div class="stat-card">
                <div class="stat-label">⚠️ Register Mismatches</div>
                <div class="stat-value stat-warning">{stats['reg_mismatch']:,}</div>
            </div>
            <div class="stat-card">
                <div class="stat-label">📊 Match Rate</div>
                <div class="stat-value stat-{'match' if match_rate > 90 else 'warning'}">{match_rate:.1f}%</div>
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
        
        <div class="controls">
            <button class="btn" onclick="filterRows('all')">Show All</button>
            <button class="btn" onclick="filterRows('mismatch')">Show Mismatches Only</button>
            <button class="btn" onclick="filterRows('match')">Show Matches Only</button>
            <div class="filter-group">
                <label>
                    <input type="checkbox" id="autoScroll" checked> Auto-scroll to first error
                </label>
            </div>
        </div>
        
        <div style="overflow-x: auto; max-height: 800px; overflow-y: auto;">
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
                <tbody>
"""
    
    # Generate table rows
    maxlen = max(len(rtl), len(spike))
    first_error = -1
    
    for i in range(maxlen):
        rtl_entry = rtl[i] if i < len(rtl) else None
        spike_entry = spike[i] if i < len(spike) else None
        disasm_cell = ''
        # Determine status
        if rtl_entry and spike_entry:
            if entries_equal(rtl_entry, spike_entry):
                if rtl_entry[2].replace(" ","") == spike_entry[2].replace(" ",""):
                    status = "match"
                    status_text = "✅ MATCH"
                    row_class = "match-row"
                else:
                    status = "reg-warn"
                    status_text = "⚠️ REG"
                    row_class = "warn-row"
                    if first_error == -1:
                        first_error = i
            else:
                status = "mismatch"
                status_text = "❌ DIFF"
                row_class = "error-row"
                if first_error == -1:
                    first_error = i
        elif rtl_entry:
            status = "extra"
            status_text = "➕ RTL"
            row_class = "extra-row"
        else:
            status = "extra"
            status_text = "➕ SPIKE"
            row_class = "extra-row"
        
        # Check for pass/fail address highlighting
        addr_highlight = ""
        if rtl_entry:
            if pass_addr is not None and rtl_entry[0] == pass_addr:
                addr_highlight = "pass-addr-highlight"
            elif fail_addr is not None and rtl_entry[0] == fail_addr:
                addr_highlight = "fail-addr-highlight"
        
        # Format cells
        rtl_html = ""
        spike_html = ""
        disasm_html = ""
        
        if rtl_entry:
            rtl_html = f'<span class="pc">PC=0x{rtl_entry[0]:08x}</span> <span class="inst">INST=0x{rtl_entry[1]:08x}</span> <span class="reg">{rtl_entry[2]}</span>'
            
            # Get disassembly if available
            if disasm_map and rtl_entry[0] in disasm_map:
                inst_hex, disasm_str = disasm_map[rtl_entry[0]]
                disasm_html = f'{disasm_str}'
        
        if spike_entry:
            spike_html = f'<span class="pc">PC=0x{spike_entry[0]:08x}</span> <span class="inst">INST=0x{spike_entry[1]:08x}</span> <span class="reg">{spike_entry[2]}</span>'
        
        # Highlight differences
        if rtl_entry and spike_entry and not entries_equal(rtl_entry, spike_entry):
            if rtl_entry[0] != spike_entry[0]:
                rtl_html = rtl_html.replace(f'0x{rtl_entry[0]:08x}', f'<span class="highlight-diff">0x{rtl_entry[0]:08x}</span>')
                spike_html = spike_html.replace(f'0x{spike_entry[0]:08x}', f'<span class="highlight-diff">0x{spike_entry[0]:08x}</span>')
            if rtl_entry[1] != spike_entry[1]:
                rtl_html = rtl_html.replace(f'0x{rtl_entry[1]:08x}', f'<span class="highlight-diff">0x{rtl_entry[1]:08x}</span>')
                spike_html = spike_html.replace(f'0x{spike_entry[1]:08x}', f'<span class="highlight-diff">0x{spike_entry[1]:08x}</span>')
            disasm_cell = ''
            if disasm_map:
                if disasm_html:
                    disasm_cell = f'<td class="disasm-col">{disasm_html}</td>'
                else:
                    disasm_cell = '<td class="disasm-col"><span style="color:#6272a4;">—</span></td>'
            else:
                disasm_cell = ''


        
        html_content += f"""
                    <tr class="{row_class} {addr_highlight}" data-status="{status}" id="row{i}">
                        <td class="cycle-num">{i+1}</td>
                        <td class="status-col"><span class="status-badge {status}">{status_text}</span></td>
                        <td class="code-cell">{rtl_html if rtl_html else '<span style="color:#6272a4;">—</span>'}</td>
                        <td class="code-cell">{spike_html if spike_html else '<span style="color:#6272a4;">—</span>'}</td>
                        {disasm_cell}
                    </tr>
"""
    
    html_content += f"""
                </tbody>
            </table>
        </div>
        
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
            <div style="margin-top: 15px;">
                CERES RISC-V Processor Verification Suite
            </div>
        </footer>
    </div>
    
    <script>
        function filterRows(type) {{
            const rows = document.querySelectorAll('.diff-table tbody tr');
            rows.forEach(row => {{
                const status = row.getAttribute('data-status');
                if (type === 'all') {{
                    row.style.display = '';
                }} else if (type === 'mismatch') {{
                    row.style.display = (status === 'mismatch' || status === 'reg-warn') ? '' : 'none';
                }} else if (type === 'match') {{
                    row.style.display = status === 'match' ? '' : 'none';
                }}
            }});
        }}
        
        // Auto-scroll to first error
        window.addEventListener('load', () => {{
            if (document.getElementById('autoScroll').checked && {first_error} >= 0) {{
                setTimeout(() => {{
                    document.getElementById('row{first_error}').scrollIntoView({{
                        behavior: 'smooth',
                        block: 'center'
                    }});
                }}, 500);
            }}
        }});
    </script>
</body>
</html>
"""
    
    with open(html_path, "w") as f:
        f.write(html_content)
    
    print(f"{Fore.CYAN}🌐 Enhanced HTML diff written to {html_path}{Style.RESET_ALL}")