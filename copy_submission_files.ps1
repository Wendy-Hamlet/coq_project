# Copy submission files to SubmissionFiles directory

Write-Host "=== Copying Submission Files ===" -ForegroundColor Cyan

$SubmissionDir = "TheoryTask\SubmissionFiles"
$QcpDir = "TheoryTask\qcp-binary-democases"
$QcpExamples = "$QcpDir\QCP_examples"
$SlExamples = "$QcpDir\SeparationLogic\examples"

# Create directory if not exists
if (-not (Test-Path $SubmissionDir)) {
    New-Item -ItemType Directory -Path $SubmissionDir | Out-Null
}

Write-Host "Copying C source files..." -ForegroundColor Yellow
Copy-Item "$QcpExamples\sll_project_def.h" "$SubmissionDir\" -Force
Copy-Item "$QcpExamples\sll_project_lib.c" "$SubmissionDir\" -Force
Copy-Item "$QcpExamples\sll_project.strategies" "$SubmissionDir\" -Force

Write-Host "Copying Coq verification files..." -ForegroundColor Yellow
Copy-Item "$SlExamples\sll_project_lib.v" "$SubmissionDir\" -Force
Copy-Item "$SlExamples\sll_project_goal.v" "$SubmissionDir\" -Force
Copy-Item "$SlExamples\sll_project_goal_check.v" "$SubmissionDir\" -Force
Copy-Item "$SlExamples\sll_project_proof_auto.v" "$SubmissionDir\" -Force
Copy-Item "$SlExamples\sll_project_proof_manual.v" "$SubmissionDir\" -Force
Copy-Item "$SlExamples\sll_project_strategy_goal.v" "$SubmissionDir\" -Force
Copy-Item "$SlExamples\sll_project_strategy_goal_check.v" "$SubmissionDir\" -Force
Copy-Item "$SlExamples\sll_project_strategy_proof.v" "$SubmissionDir\" -Force

Write-Host "`nCopy complete! Files are in $SubmissionDir\" -ForegroundColor Green

$fileCount = (Get-ChildItem $SubmissionDir -Filter *.* | Where-Object { $_.Extension -match '\.(h|c|strategies|v)$' }).Count
Write-Host "`nFile count: $fileCount files (expected: 11)" -ForegroundColor Cyan
