# Build script for TheoryTask Coq verification
# This script sets up the environment and generates verification files

param(
    [switch]$SkipSetup,
    [switch]$CleanOnly
)

$ErrorActionPreference = "Stop"

Write-Host "=== TheoryTask Build Script ===" -ForegroundColor Cyan

# Step 1: Environment Setup
if (-not $SkipSetup) {
    Write-Host "`n[1/5] Pulling latest code..." -ForegroundColor Yellow
    git pull
    if ($LASTEXITCODE -ne 0) { 
        Write-Host "Warning: git pull failed, continuing anyway..." -ForegroundColor Yellow 
    }

    Write-Host "`n[2/5] Updating submodules..." -ForegroundColor Yellow
    git submodule update --init --recursive
    if ($LASTEXITCODE -ne 0) { 
        Write-Error "Submodule update failed!" 
        exit 1 
    }

    Write-Host "`n[3/5] Building unifysl library..." -ForegroundColor Yellow
    Push-Location TheoryTask\qcp-binary-democases\SeparationLogic\unifysl
    make depend
    make
    if ($LASTEXITCODE -ne 0) { 
        Pop-Location
        Write-Error "unifysl build failed!" 
        exit 1 
    }
    Pop-Location

    Write-Host "`n[4/5] Building SeparationLogic library..." -ForegroundColor Yellow
    Push-Location TheoryTask\qcp-binary-democases\SeparationLogic
    make depend
    make
    if ($LASTEXITCODE -ne 0) { 
        Pop-Location
        Write-Error "SeparationLogic build failed!" 
        exit 1 
    }
    Pop-Location

    Write-Host "`n[5/5] Environment setup complete!" -ForegroundColor Green
} else {
    Write-Host "Skipping environment setup (use -SkipSetup:$false to include)" -ForegroundColor Yellow
}

# Check if we should stop here
if ($CleanOnly) {
    Write-Host "`nClean-only mode. Exiting." -ForegroundColor Cyan
    exit 0
}

# Step 2: Generate verification files (requires Cygwin/WSL)
Write-Host "`n=== Generating Verification Files ===" -ForegroundColor Cyan
Write-Host "This step requires Cygwin, WSL, or a Unix-like environment." -ForegroundColor Yellow
Write-Host "Please run the following commands manually in Cygwin/WSL:" -ForegroundColor Yellow
Write-Host ""
Write-Host "cd TheoryTask/qcp-binary-democases" -ForegroundColor White
Write-Host ""
Write-Host "# Clean old generated files" -ForegroundColor Gray
Write-Host "rm -f SeparationLogic/examples/sll_project_goal.v \"  -ForegroundColor White -NoNewline
Write-Host "SeparationLogic/examples/sll_project_goal_check.v \"  -ForegroundColor White -NoNewline
Write-Host "SeparationLogic/examples/sll_project_proof_auto.v \"  -ForegroundColor White -NoNewline
Write-Host "SeparationLogic/examples/sll_project_proof_manual.v \"  -ForegroundColor White -NoNewline
Write-Host "SeparationLogic/examples/sll_project_strategy_goal.v \"  -ForegroundColor White -NoNewline
Write-Host "SeparationLogic/examples/sll_project_strategy_goal_check.v \"  -ForegroundColor White -NoNewline
Write-Host "SeparationLogic/examples/sll_project_strategy_proof.v" -ForegroundColor White
Write-Host ""
Write-Host "# Generate C program verification files" -ForegroundColor Gray
Write-Host "win-binary/symexec.exe --goal-file=SeparationLogic/examples/sll_project_goal.v --proof-auto-file=SeparationLogic/examples/sll_project_proof_auto.v --proof-manual-file=SeparationLogic/examples/sll_project_proof_manual.v -I QCP_examples/ -slp QCP_examples/ SimpleC.EE --input-file=QCP_examples/sll_project_lib.c --no-exec-info" -ForegroundColor White
Write-Host ""
Write-Host "# Generate strategy verification files" -ForegroundColor Gray
Write-Host "win-binary/StrategyCheck.exe --strategy-folder-path=SeparationLogic/examples/ --coq-logic-path=SimpleC.EE --input-file=QCP_examples/sll_project.strategies --no-exec-info" -ForegroundColor White
Write-Host ""
Write-Host "# Compile generated Coq files" -ForegroundColor Gray
Write-Host "cd SeparationLogic" -ForegroundColor White
Write-Host "make depend && make" -ForegroundColor White
Write-Host ""
Write-Host "Press Enter when you have completed the above steps..." -ForegroundColor Yellow
Read-Host

Write-Host "`n=== Build Complete ===" -ForegroundColor Green
Write-Host "All verification files have been generated and compiled." -ForegroundColor Green

# Copy submission files
Write-Host ""
Write-Host "Copying files to TheoryTask/SubmissionFiles/..." -ForegroundColor Cyan
& .\copy_submission_files.ps1
