# Deploying Cost Model Visualization to GitHub Pages

## Current GitHub Pages Configuration

The Plutus repository uses GitHub Pages with the following setup:

- **Branch**: `gh-pages`
- **URL**: <https://plutus.cardano.intersectmbo.org/>
- **Current content**: Docusaurus site at `/docs` and Haddock at `/haddock`

## Deployment Strategy

Add the cost model visualizations to the existing `gh-pages` branch under a new path: `/cost-models/`

### Step 1: Checkout gh-pages branch

```bash
cd /home/yura/projects/cardano/plutus

# Fetch latest gh-pages
git fetch origin gh-pages

# Create a worktree for gh-pages (keeps your current branch intact)
git worktree add ../plutus-gh-pages gh-pages

# Navigate to the worktree
cd ../plutus-gh-pages
```

### Step 2: Add visualization to gh-pages

```bash
# Create cost-models directory
mkdir -p cost-models

# Copy visualization files
cp -r /home/yura/projects/cardano/plutus/plutus-core/cost-model/data/web/* cost-models/

# Stage changes
git add cost-models/

# Commit
git commit -m "Add interactive cost model visualizations"

# Push to gh-pages
git push origin gh-pages
```

### Step 3: Access the deployed site

The visualizations will be available at:

- **Main page**: <https://plutus.cardano.intersectmbo.org/cost-models/>
- **ValueData**: <https://plutus.cardano.intersectmbo.org/cost-models/valuedata/>
- **UnValueData**: <https://plutus.cardano.intersectmbo.org/cost-models/unvaluedata/>
- **ValueContains**: <https://plutus.cardano.intersectmbo.org/cost-models/valuecontains/>
- **LookupCoin**: <https://plutus.cardano.intersectmbo.org/cost-models/lookupcoin/>

### Step 4: Cleanup (optional)

```bash
# Return to main repository
cd /home/yura/projects/cardano/plutus

# Remove the worktree when done
git worktree remove ../plutus-gh-pages
```

## Alternative: Add to Docusaurus Site

If you want to integrate with the existing Docusaurus documentation:

1. Add visualization to `doc/docusaurus/static/cost-models/`
2. The Docusaurus workflow will deploy it automatically on push to master
3. Access at: <https://plutus.cardano.intersectmbo.org/docs/cost-models/>

## Updating the Visualizations

### Manual Update

```bash
cd /home/yura/projects/cardano/plutus

# Update via worktree
git worktree add ../plutus-gh-pages gh-pages
cd ../plutus-gh-pages

# Update files
cp -r /home/yura/projects/cardano/plutus/plutus-core/cost-model/data/web/* cost-models/

# Commit and push
git add cost-models/
git commit -m "Update cost model visualizations"
git push origin gh-pages

# Cleanup
cd /home/yura/projects/cardano/plutus
git worktree remove ../plutus-gh-pages
```

### Automated Update (Future Enhancement)

Create a GitHub Actions workflow similar to `docusaurus-site.yml` that:

1. Triggers on changes to `plutus-core/cost-model/data/web/**`
2. Copies web files to `cost-models/` directory on `gh-pages`
3. Auto-commits and pushes

Example workflow location: `.github/workflows/cost-model-viz.yml`

## Testing with Branch Data

Once deployed, you can test visualizations with data from any branch:

1. Open a visualization page (e.g., ValueData)
2. Expand "Data Source Configuration"
3. Change branch name from `master` to your branch (e.g., `yura/costing-builtin-value`)
4. Click "Load Data"

The URLs will automatically update to:
```
https://raw.githubusercontent.com/IntersectMBO/plutus/yura/costing-builtin-value/plutus-core/cost-model/data/benching-conway.csv
https://raw.githubusercontent.com/IntersectMBO/plutus/yura/costing-builtin-value/plutus-core/cost-model/data/builtinCostModelC.json
```

## Notes

- The `gh-pages` branch is managed by GitHub Actions (see `docusaurus-site.yml`)
- Current structure: root redirects to `/docs`, actual content in subdirectories
- The branch uses `JamesIves/github-pages-deploy-action` for deployment
- Changes to `gh-pages` should be coordinated with the documentation team to avoid conflicts
- The site uses a custom domain: `plutus.cardano.intersectmbo.org`

## Recommended Approach

**For testing/development:**
- Use the branch name input to point to your development branch
- No deployment needed

**For production deployment:**
- Coordinate with repository maintainers
- Consider adding to Docusaurus static files instead of raw gh-pages
- Or create a dedicated workflow for automatic deployment
