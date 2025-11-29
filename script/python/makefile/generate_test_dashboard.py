#!/usr/bin/env python3
"""
generate_test_dashboard.py — Test Results Dashboard Generator
==============================================================
Generates an interactive HTML dashboard showing all test results
with navigation to individual test reports.

Features:
  ✅ Scans results directory for test HTML reports
  ✅ Parses status from diff.log files
  ✅ Groups tests by category (ui, um, uc, etc.)
  ✅ Beautiful responsive dashboard
  ✅ Quick filtering and search
  ✅ Summary statistics with charts
  ✅ Dark/Light theme support
"""

import os
import re
import json
import argparse
from datetime import datetime
from pathlib import Path


def parse_diff_log(diff_log_path):
    """Parse diff.log file to get test status and statistics."""
    result = {
        "status": "unknown",
        "match": 0,
        "pcinst_mismatch": 0,
        "reg_mismatch": 0,
        "rtl_extra": 0,
        "spike_extra": 0,
        "match_rate": 0.0
    }
    
    try:
        with open(diff_log_path, 'r') as f:
            content = f.read()
            
            # Parse status
            if "DIFF_STATUS=MATCH" in content:
                result["status"] = "pass"
            elif "DIFF_STATUS=MISMATCH" in content:
                result["status"] = "fail"
            
            # Parse statistics
            match = re.search(r'Perfect Matches\s*:\s*(\d+)', content)
            if match:
                result["match"] = int(match.group(1))
            
            match = re.search(r'PC/INST Mismatches\s*:\s*(\d+)', content)
            if match:
                result["pcinst_mismatch"] = int(match.group(1))
            
            match = re.search(r'Register Mismatches\s*:\s*(\d+)', content)
            if match:
                result["reg_mismatch"] = int(match.group(1))
            
            match = re.search(r'RTL Extra Entries\s*:\s*(\d+)', content)
            if match:
                result["rtl_extra"] = int(match.group(1))
            
            match = re.search(r'Spike Extra Entries\s*:\s*(\d+)', content)
            if match:
                result["spike_extra"] = int(match.group(1))
            
            match = re.search(r'Match Rate\s*:\s*([\d.]+)%', content)
            if match:
                result["match_rate"] = float(match.group(1))
                
    except FileNotFoundError:
        result["status"] = "missing"
    except Exception as e:
        result["status"] = "error"
        result["error"] = str(e)
    
    return result


def get_test_category(test_name):
    """Extract test category from test name."""
    # rv32ui-p-add -> ui
    # rv32um-p-mul -> um
    # rv32uc-p-rvc -> uc
    match = re.match(r'rv\d+(\w+)-', test_name)
    if match:
        return match.group(1)
    return "other"


def get_test_instruction(test_name):
    """Extract instruction name from test name."""
    # rv32ui-p-add -> add
    parts = test_name.split('-')
    if len(parts) >= 3:
        return parts[-1]
    return test_name


def scan_test_results(results_dir, simulator="verilator"):
    """Scan results directory and collect test information."""
    tests = []
    sim_dir = os.path.join(results_dir, "logs", simulator)
    
    if not os.path.exists(sim_dir):
        print(f"Warning: Directory not found: {sim_dir}")
        return tests
    
    for test_name in os.listdir(sim_dir):
        test_path = os.path.join(sim_dir, test_name)
        
        if not os.path.isdir(test_path):
            continue
        
        # Skip special directories
        if test_name in ['coverage_data']:
            continue
        
        html_file = os.path.join(test_path, "diff.html")
        diff_log = os.path.join(test_path, "diff.log")
        
        test_info = {
            "name": test_name,
            "category": get_test_category(test_name),
            "instruction": get_test_instruction(test_name),
            "html_exists": os.path.exists(html_file),
            "html_path": f"{simulator}/{test_name}/diff.html" if os.path.exists(html_file) else None,
            "log_path": f"{simulator}/{test_name}/diff.log",
        }
        
        # Parse statistics from diff.log
        stats = parse_diff_log(diff_log)
        test_info.update(stats)
        
        tests.append(test_info)
    
    # Sort by category then name
    tests.sort(key=lambda x: (x["category"], x["name"]))
    
    return tests


def generate_dashboard_html(tests, output_path, title="CERES Test Dashboard"):
    """Generate the main dashboard HTML page."""
    
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    
    # Calculate summary statistics
    total = len(tests)
    passed = sum(1 for t in tests if t["status"] == "pass")
    failed = sum(1 for t in tests if t["status"] == "fail")
    missing = sum(1 for t in tests if t["status"] == "missing")
    unknown = total - passed - failed - missing
    pass_rate = (passed / total * 100) if total > 0 else 0
    
    # Group by category
    categories = {}
    for test in tests:
        cat = test["category"]
        if cat not in categories:
            categories[cat] = {"tests": [], "passed": 0, "failed": 0}
        categories[cat]["tests"].append(test)
        if test["status"] == "pass":
            categories[cat]["passed"] += 1
        elif test["status"] == "fail":
            categories[cat]["failed"] += 1
    
    # Convert to JSON for JavaScript
    tests_json = json.dumps(tests)
    categories_json = json.dumps({k: {"passed": v["passed"], "failed": v["failed"], "total": len(v["tests"])} 
                                  for k, v in categories.items()})
    
    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title}</title>
    <style>
        :root {{
            --bg-primary: #1a1a2e;
            --bg-secondary: #16213e;
            --bg-tertiary: #0f3460;
            --bg-card: #1f2940;
            --text-primary: #eaeaea;
            --text-secondary: #a0a0a0;
            --accent: #e94560;
            --accent-hover: #ff6b6b;
            --pass: #00d26a;
            --fail: #ff4757;
            --warning: #ffc107;
            --info: #00b8d4;
            --border: #2a3f5f;
        }}
        
        [data-theme="light"] {{
            --bg-primary: #f5f7fa;
            --bg-secondary: #ffffff;
            --bg-tertiary: #e8ecf1;
            --bg-card: #ffffff;
            --text-primary: #2d3748;
            --text-secondary: #718096;
            --accent: #e94560;
            --accent-hover: #ff6b6b;
            --pass: #28a745;
            --fail: #dc3545;
            --warning: #ffc107;
            --info: #17a2b8;
            --border: #e2e8f0;
        }}
        
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}
        
        body {{
            font-family: 'Segoe UI', 'Inter', -apple-system, BlinkMacSystemFont, sans-serif;
            background: var(--bg-primary);
            color: var(--text-primary);
            min-height: 100vh;
            line-height: 1.6;
        }}
        
        /* Header */
        .header {{
            background: linear-gradient(135deg, var(--bg-secondary) 0%, var(--bg-tertiary) 100%);
            padding: 30px 40px;
            border-bottom: 3px solid var(--accent);
            position: sticky;
            top: 0;
            z-index: 100;
        }}
        
        .header-content {{
            max-width: 1600px;
            margin: 0 auto;
            display: flex;
            justify-content: space-between;
            align-items: center;
            flex-wrap: wrap;
            gap: 20px;
        }}
        
        .logo {{
            display: flex;
            align-items: center;
            gap: 15px;
        }}
        
        .logo-icon {{
            font-size: 2.5em;
        }}
        
        .logo h1 {{
            font-size: 1.8em;
            font-weight: 700;
            background: linear-gradient(135deg, var(--accent), var(--info));
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            background-clip: text;
        }}
        
        .logo .subtitle {{
            font-size: 0.85em;
            color: var(--text-secondary);
        }}
        
        .header-actions {{
            display: flex;
            gap: 15px;
            align-items: center;
        }}
        
        .theme-toggle {{
            background: var(--bg-card);
            border: 2px solid var(--border);
            color: var(--text-primary);
            padding: 10px 20px;
            border-radius: 25px;
            cursor: pointer;
            font-size: 1em;
            transition: all 0.3s;
            display: flex;
            align-items: center;
            gap: 8px;
        }}
        
        .theme-toggle:hover {{
            border-color: var(--accent);
            transform: translateY(-2px);
        }}
        
        /* Summary Cards */
        .summary-section {{
            max-width: 1600px;
            margin: 30px auto;
            padding: 0 40px;
        }}
        
        .summary-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 20px;
            margin-bottom: 30px;
        }}
        
        .summary-card {{
            background: var(--bg-card);
            border-radius: 16px;
            padding: 25px;
            border: 2px solid var(--border);
            transition: all 0.3s;
            position: relative;
            overflow: hidden;
        }}
        
        .summary-card::before {{
            content: '';
            position: absolute;
            top: 0;
            left: 0;
            right: 0;
            height: 4px;
        }}
        
        .summary-card.total::before {{ background: var(--info); }}
        .summary-card.passed::before {{ background: var(--pass); }}
        .summary-card.failed::before {{ background: var(--fail); }}
        .summary-card.rate::before {{ background: var(--accent); }}
        
        .summary-card:hover {{
            transform: translateY(-5px);
            box-shadow: 0 10px 30px rgba(0, 0, 0, 0.2);
        }}
        
        .summary-card .label {{
            font-size: 0.9em;
            color: var(--text-secondary);
            text-transform: uppercase;
            letter-spacing: 1px;
            margin-bottom: 10px;
        }}
        
        .summary-card .value {{
            font-size: 2.5em;
            font-weight: 700;
        }}
        
        .summary-card.total .value {{ color: var(--info); }}
        .summary-card.passed .value {{ color: var(--pass); }}
        .summary-card.failed .value {{ color: var(--fail); }}
        .summary-card.rate .value {{ color: var(--accent); }}
        
        /* Progress Bar */
        .progress-section {{
            background: var(--bg-card);
            border-radius: 16px;
            padding: 25px;
            border: 2px solid var(--border);
            margin-bottom: 30px;
        }}
        
        .progress-header {{
            display: flex;
            justify-content: space-between;
            margin-bottom: 15px;
        }}
        
        .progress-bar {{
            height: 24px;
            background: var(--bg-tertiary);
            border-radius: 12px;
            overflow: hidden;
            display: flex;
        }}
        
        .progress-pass {{
            background: linear-gradient(90deg, #00d26a, #00f2a0);
            height: 100%;
            transition: width 0.5s ease;
        }}
        
        .progress-fail {{
            background: linear-gradient(90deg, #ff4757, #ff6b81);
            height: 100%;
            transition: width 0.5s ease;
        }}
        
        /* Controls */
        .controls {{
            max-width: 1600px;
            margin: 0 auto 30px;
            padding: 0 40px;
            display: flex;
            gap: 15px;
            flex-wrap: wrap;
            align-items: center;
        }}
        
        .search-box {{
            flex: 1;
            min-width: 250px;
            max-width: 400px;
            position: relative;
        }}
        
        .search-box input {{
            width: 100%;
            padding: 14px 20px 14px 50px;
            background: var(--bg-card);
            border: 2px solid var(--border);
            border-radius: 12px;
            color: var(--text-primary);
            font-size: 1em;
            transition: all 0.3s;
        }}
        
        .search-box input:focus {{
            outline: none;
            border-color: var(--accent);
            box-shadow: 0 0 0 3px rgba(233, 69, 96, 0.2);
        }}
        
        .search-box::before {{
            content: "🔍";
            position: absolute;
            left: 18px;
            top: 50%;
            transform: translateY(-50%);
            font-size: 1.2em;
        }}
        
        .filter-group {{
            display: flex;
            gap: 8px;
        }}
        
        .filter-btn {{
            padding: 12px 24px;
            background: var(--bg-card);
            border: 2px solid var(--border);
            color: var(--text-primary);
            border-radius: 10px;
            cursor: pointer;
            font-size: 0.95em;
            transition: all 0.3s;
            font-weight: 500;
        }}
        
        .filter-btn:hover {{
            border-color: var(--accent);
        }}
        
        .filter-btn.active {{
            background: var(--accent);
            border-color: var(--accent);
            color: white;
        }}
        
        .category-select {{
            padding: 14px 20px;
            background: var(--bg-card);
            border: 2px solid var(--border);
            border-radius: 12px;
            color: var(--text-primary);
            font-size: 1em;
            cursor: pointer;
            min-width: 150px;
        }}
        
        /* Tests Grid */
        .tests-section {{
            max-width: 1600px;
            margin: 0 auto;
            padding: 0 40px 40px;
        }}
        
        .tests-header {{
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 20px;
        }}
        
        .tests-header h2 {{
            font-size: 1.5em;
            color: var(--text-primary);
        }}
        
        .tests-count {{
            color: var(--text-secondary);
            font-size: 0.95em;
        }}
        
        .tests-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
            gap: 20px;
        }}
        
        .test-card {{
            background: var(--bg-card);
            border-radius: 14px;
            padding: 20px;
            border: 2px solid var(--border);
            transition: all 0.3s;
            cursor: pointer;
            position: relative;
            overflow: hidden;
        }}
        
        .test-card:hover {{
            transform: translateY(-3px);
            box-shadow: 0 8px 25px rgba(0, 0, 0, 0.15);
            border-color: var(--accent);
        }}
        
        .test-card.pass {{
            border-left: 4px solid var(--pass);
        }}
        
        .test-card.fail {{
            border-left: 4px solid var(--fail);
        }}
        
        .test-card.missing {{
            border-left: 4px solid var(--warning);
            opacity: 0.7;
        }}
        
        .test-card-header {{
            display: flex;
            justify-content: space-between;
            align-items: flex-start;
            margin-bottom: 12px;
        }}
        
        .test-name {{
            font-size: 1.1em;
            font-weight: 600;
            color: var(--text-primary);
            word-break: break-word;
        }}
        
        .test-status {{
            padding: 5px 12px;
            border-radius: 20px;
            font-size: 0.8em;
            font-weight: 600;
            text-transform: uppercase;
        }}
        
        .test-status.pass {{
            background: rgba(0, 210, 106, 0.15);
            color: var(--pass);
        }}
        
        .test-status.fail {{
            background: rgba(255, 71, 87, 0.15);
            color: var(--fail);
        }}
        
        .test-status.missing {{
            background: rgba(255, 193, 7, 0.15);
            color: var(--warning);
        }}
        
        .test-meta {{
            display: flex;
            gap: 15px;
            margin-bottom: 12px;
            font-size: 0.9em;
            color: var(--text-secondary);
        }}
        
        .test-meta span {{
            display: flex;
            align-items: center;
            gap: 5px;
        }}
        
        .test-stats {{
            display: grid;
            grid-template-columns: repeat(3, 1fr);
            gap: 10px;
            padding-top: 12px;
            border-top: 1px solid var(--border);
        }}
        
        .test-stat {{
            text-align: center;
        }}
        
        .test-stat .stat-value {{
            font-size: 1.2em;
            font-weight: 700;
        }}
        
        .test-stat .stat-label {{
            font-size: 0.75em;
            color: var(--text-secondary);
            text-transform: uppercase;
        }}
        
        .test-stat.match .stat-value {{ color: var(--pass); }}
        .test-stat.mismatch .stat-value {{ color: var(--fail); }}
        .test-stat.rate .stat-value {{ color: var(--info); }}
        
        .test-link {{
            display: block;
            text-align: center;
            margin-top: 15px;
            padding: 10px;
            background: var(--bg-tertiary);
            border-radius: 8px;
            color: var(--accent);
            text-decoration: none;
            font-weight: 500;
            transition: all 0.3s;
        }}
        
        .test-link:hover {{
            background: var(--accent);
            color: white;
        }}
        
        /* Category badges */
        .category-badge {{
            display: inline-block;
            padding: 3px 10px;
            background: var(--bg-tertiary);
            border-radius: 15px;
            font-size: 0.8em;
            color: var(--text-secondary);
            text-transform: uppercase;
        }}
        
        /* Footer */
        .footer {{
            text-align: center;
            padding: 30px;
            color: var(--text-secondary);
            font-size: 0.9em;
            border-top: 1px solid var(--border);
            margin-top: 40px;
        }}
        
        /* Category Section */
        .category-section {{
            margin-bottom: 40px;
        }}
        
        .category-header {{
            display: flex;
            align-items: center;
            gap: 15px;
            margin-bottom: 20px;
            padding-bottom: 10px;
            border-bottom: 2px solid var(--border);
        }}
        
        .category-title {{
            font-size: 1.3em;
            font-weight: 600;
            text-transform: uppercase;
        }}
        
        .category-stats {{
            display: flex;
            gap: 10px;
            font-size: 0.9em;
        }}
        
        .category-stats span {{
            padding: 4px 12px;
            border-radius: 15px;
        }}
        
        .category-stats .pass {{
            background: rgba(0, 210, 106, 0.15);
            color: var(--pass);
        }}
        
        .category-stats .fail {{
            background: rgba(255, 71, 87, 0.15);
            color: var(--fail);
        }}
        
        /* Responsive */
        @media (max-width: 768px) {{
            .header {{
                padding: 20px;
            }}
            
            .summary-section, .controls, .tests-section {{
                padding: 0 20px;
            }}
            
            .logo h1 {{
                font-size: 1.4em;
            }}
            
            .tests-grid {{
                grid-template-columns: 1fr;
            }}
            
            .filter-group {{
                width: 100%;
                justify-content: center;
            }}
        }}
        
        /* Empty State */
        .empty-state {{
            text-align: center;
            padding: 60px 20px;
            color: var(--text-secondary);
        }}
        
        .empty-state .icon {{
            font-size: 4em;
            margin-bottom: 20px;
        }}
    </style>
</head>
<body>
    <header class="header">
        <div class="header-content">
            <div class="logo">
                <span class="logo-icon">🔬</span>
                <div>
                    <h1>CERES Test Dashboard</h1>
                    <div class="subtitle">RISC-V Processor Verification Results</div>
                </div>
            </div>
            <div class="header-actions">
                <span style="color: var(--text-secondary);">Generated: {timestamp}</span>
                <button class="theme-toggle" onclick="toggleTheme()">
                    <span id="themeIcon">🌙</span>
                    <span>Theme</span>
                </button>
            </div>
        </div>
    </header>
    
    <section class="summary-section">
        <div class="summary-grid">
            <div class="summary-card total">
                <div class="label">Total Tests</div>
                <div class="value">{total}</div>
            </div>
            <div class="summary-card passed">
                <div class="label">Passed</div>
                <div class="value">{passed}</div>
            </div>
            <div class="summary-card failed">
                <div class="label">Failed</div>
                <div class="value">{failed}</div>
            </div>
            <div class="summary-card rate">
                <div class="label">Pass Rate</div>
                <div class="value">{pass_rate:.1f}%</div>
            </div>
        </div>
        
        <div class="progress-section">
            <div class="progress-header">
                <span>Overall Progress</span>
                <span>{passed} / {total} tests passing</span>
            </div>
            <div class="progress-bar">
                <div class="progress-pass" style="width: {pass_rate}%"></div>
                <div class="progress-fail" style="width: {(failed/total*100) if total > 0 else 0}%"></div>
            </div>
        </div>
    </section>
    
    <section class="controls">
        <div class="search-box">
            <input type="text" id="searchInput" placeholder="Search tests..." onkeyup="filterTests()">
        </div>
        
        <div class="filter-group">
            <button class="filter-btn active" data-filter="all" onclick="setFilter('all', this)">All</button>
            <button class="filter-btn" data-filter="pass" onclick="setFilter('pass', this)">✅ Passed</button>
            <button class="filter-btn" data-filter="fail" onclick="setFilter('fail', this)">❌ Failed</button>
        </div>
        
        <select class="category-select" id="categorySelect" onchange="filterTests()">
            <option value="all">All Categories</option>
            {"".join(f'<option value="{cat}">{cat.upper()} ({len(data["tests"])} tests)</option>' for cat, data in sorted(categories.items()))}
        </select>
    </section>
    
    <section class="tests-section">
        <div class="tests-header">
            <h2>Test Results</h2>
            <span class="tests-count" id="testsCount">Showing {total} tests</span>
        </div>
        
        <div class="tests-grid" id="testsGrid">
            <!-- Tests will be rendered by JavaScript -->
        </div>
        
        <div class="empty-state" id="emptyState" style="display: none;">
            <div class="icon">🔍</div>
            <h3>No tests found</h3>
            <p>Try adjusting your search or filters</p>
        </div>
    </section>
    
    <footer class="footer">
        <p>CERES RISC-V Processor — Test Verification Dashboard</p>
        <p>Generated by CERES Test Suite</p>
    </footer>
    
    <script>
        const allTests = {tests_json};
        let currentFilter = 'all';
        let searchQuery = '';
        let selectedCategory = 'all';
        
        function renderTests() {{
            const grid = document.getElementById('testsGrid');
            const emptyState = document.getElementById('emptyState');
            const countEl = document.getElementById('testsCount');
            
            let filtered = allTests.filter(test => {{
                // Status filter
                if (currentFilter !== 'all' && test.status !== currentFilter) return false;
                
                // Category filter
                if (selectedCategory !== 'all' && test.category !== selectedCategory) return false;
                
                // Search filter
                if (searchQuery) {{
                    const q = searchQuery.toLowerCase();
                    if (!test.name.toLowerCase().includes(q) && 
                        !test.instruction.toLowerCase().includes(q) &&
                        !test.category.toLowerCase().includes(q)) {{
                        return false;
                    }}
                }}
                
                return true;
            }});
            
            if (filtered.length === 0) {{
                grid.innerHTML = '';
                emptyState.style.display = 'block';
                countEl.textContent = 'No tests found';
                return;
            }}
            
            emptyState.style.display = 'none';
            countEl.textContent = `Showing ${{filtered.length}} of ${{allTests.length}} tests`;
            
            let html = '';
            filtered.forEach(test => {{
                const statusClass = test.status;
                const statusText = test.status === 'pass' ? 'PASS' : 
                                   test.status === 'fail' ? 'FAIL' : 
                                   test.status === 'missing' ? 'NO DATA' : 'UNKNOWN';
                
                const totalMismatch = test.pcinst_mismatch + test.reg_mismatch;
                
                html += `
                    <div class="test-card ${{statusClass}}" onclick="openTest('${{test.html_path}}')">
                        <div class="test-card-header">
                            <span class="test-name">${{test.name}}</span>
                            <span class="test-status ${{statusClass}}">${{statusText}}</span>
                        </div>
                        <div class="test-meta">
                            <span class="category-badge">${{test.category.toUpperCase()}}</span>
                            <span>📝 ${{test.instruction}}</span>
                        </div>
                        <div class="test-stats">
                            <div class="test-stat match">
                                <div class="stat-value">${{test.match.toLocaleString()}}</div>
                                <div class="stat-label">Match</div>
                            </div>
                            <div class="test-stat mismatch">
                                <div class="stat-value">${{totalMismatch.toLocaleString()}}</div>
                                <div class="stat-label">Mismatch</div>
                            </div>
                            <div class="test-stat rate">
                                <div class="stat-value">${{test.match_rate.toFixed(1)}}%</div>
                                <div class="stat-label">Rate</div>
                            </div>
                        </div>
                        ${{test.html_exists ? '<a class="test-link" onclick="event.stopPropagation();" href="' + test.html_path + '">View Detailed Report →</a>' : '<span class="test-link" style="opacity:0.5;">Report Not Available</span>'}}
                    </div>
                `;
            }});
            
            grid.innerHTML = html;
        }}
        
        function openTest(htmlPath) {{
            if (htmlPath) {{
                window.location.href = htmlPath;
            }}
        }}
        
        function setFilter(filter, btn) {{
            currentFilter = filter;
            document.querySelectorAll('.filter-btn').forEach(b => b.classList.remove('active'));
            btn.classList.add('active');
            filterTests();
        }}
        
        function filterTests() {{
            searchQuery = document.getElementById('searchInput').value;
            selectedCategory = document.getElementById('categorySelect').value;
            renderTests();
        }}
        
        function toggleTheme() {{
            const html = document.documentElement;
            const current = html.getAttribute('data-theme');
            const newTheme = current === 'light' ? 'dark' : 'light';
            html.setAttribute('data-theme', newTheme);
            localStorage.setItem('dashboard-theme', newTheme);
            document.getElementById('themeIcon').textContent = newTheme === 'light' ? '☀️' : '🌙';
        }}
        
        // Initialize
        document.addEventListener('DOMContentLoaded', () => {{
            // Load saved theme
            const savedTheme = localStorage.getItem('dashboard-theme');
            if (savedTheme) {{
                document.documentElement.setAttribute('data-theme', savedTheme);
                document.getElementById('themeIcon').textContent = savedTheme === 'light' ? '☀️' : '🌙';
            }}
            
            renderTests();
        }});
        
        // Keyboard shortcuts
        document.addEventListener('keydown', (e) => {{
            if (e.key === '/') {{
                e.preventDefault();
                document.getElementById('searchInput').focus();
            }}
        }});
    </script>
</body>
</html>
"""
    
    # Ensure output directory exists
    os.makedirs(os.path.dirname(output_path) if os.path.dirname(output_path) else '.', exist_ok=True)
    
    with open(output_path, 'w') as f:
        f.write(html)
    
    print(f"✅ Dashboard generated: {output_path}")
    print(f"   📊 Total: {total} | ✅ Passed: {passed} | ❌ Failed: {failed} | 📈 Rate: {pass_rate:.1f}%")


def main():
    parser = argparse.ArgumentParser(
        description="Generate Test Results Dashboard",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --results-dir ./results --output ./results/logs/dashboard.html
  %(prog)s --results-dir ./results --simulator verilator --output dashboard.html
        """
    )
    
    parser.add_argument("--results-dir", required=True, 
                        help="Path to results directory")
    parser.add_argument("--output", required=True,
                        help="Output HTML file path")
    parser.add_argument("--simulator", default="verilator",
                        help="Simulator name (default: verilator)")
    parser.add_argument("--title", default="CERES Test Dashboard",
                        help="Dashboard title")
    
    args = parser.parse_args()
    
    print(f"🔍 Scanning {args.results_dir}/logs/{args.simulator} for test results...")
    tests = scan_test_results(args.results_dir, args.simulator)
    
    if not tests:
        print("⚠️  No tests found!")
        return 1
    
    print(f"📋 Found {len(tests)} tests")
    generate_dashboard_html(tests, args.output, args.title)
    
    return 0


if __name__ == "__main__":
    exit(main())
