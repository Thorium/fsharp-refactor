# Puts the compiled command table INSIDE a managed .resources set, which is
# what MergeWithCTO does in the VSSDK targets and what a package registered
# with UseManagedResourcesOnly makes the shell look for: ProvideMenuResource
# names an ENTRY in the set, not a standalone manifest resource stream.
param([string]$Cto, [string]$OutDir)

$bytes = [IO.File]::ReadAllBytes($Cto)

# An empty or truncated table embeds silently and produces an extension whose
# menu simply does not exist â€” no error anywhere, which is the exact failure
# this file was written during. VSCT output starts with the magic "CFCT".
if ($bytes.Length -lt 4) {
    throw "Command table '$Cto' is $($bytes.Length) bytes; VSCT did not produce it (check target ordering: EmbedCtoResources must DependsOnTargets CompileCommandTable)."
}

$magic = [Text.Encoding]::ASCII.GetString($bytes, 0, 4)
if ($magic -ne 'CFCT') {
    throw "Command table '$Cto' does not start with CFCT (got '$magic'); it is not a compiled command table."
}

foreach ($name in @('VSPackage.resources', 'FSharpRefactorPackage.resources')) {
    $path = Join-Path $OutDir $name
    $writer = New-Object System.Resources.ResourceWriter($path)
    $writer.AddResource('Menus.ctmenu', $bytes)
    $writer.Generate()
    $writer.Close()
    Write-Host "wrote $path ($($bytes.Length) byte table)"
}
