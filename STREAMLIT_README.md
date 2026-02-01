# 🎯 Carré de Dakar - Application Streamlit

## 🚀 Démarrage Rapide

### 1. Lancer l'application

```bash
cd /Users/arthursarazin/Documents/aristotle
streamlit run streamlit_app.py
```

L'application s'ouvrira automatiquement dans votre navigateur à `http://localhost:8501`

### 2. Utilisation

#### Panneau de Contrôle (Sidebar)

- **Dimension de la grille:** Ajustez de 4×4 à 15×15
- **Nombre maximum:** Définit la taille maximale des nombres dans les équations
- **Mode Puzzle:** Active le mode avec nombres cachés
- **Pourcentage caché:** Si mode puzzle activé (10% à 50%)
- **Bouton Générer:** Crée une nouvelle grille aléatoire

#### Affichage Principal

**Grille:**
- 🟢 Cellules blanches = Nombres
- 🔴 Cellules rouges = Opérateurs (+, -, ×)
- 🔵 Cellules vertes = Signe égal (=)
- 🟣 Cellules violettes = Nombres cachés (mode puzzle)

**Statistiques:**
- Dimension de la grille
- Nombre d'équations détectées
- Taux de validité

**Validation:**
- Liste des équations valides ✅
- Liste des équations invalides ❌ (s'il y en a)

## ✨ Fonctionnalités

### Mode Normal
- Génère une grille complète avec toutes les valeurs visibles
- Vérifie automatiquement toutes les équations
- Affiche les statistiques en temps réel

### Mode Puzzle
- Cache un pourcentage de nombres
- Option pour afficher/masquer la solution
- Idéal pour tester la jouabilité

### Validation Automatique
- Vérification de toutes les équations horizontales
- Vérification de toutes les équations verticales
- Détection automatique des erreurs

## 🎨 Personnalisation

### Modifier les Couleurs

Éditez la section CSS dans `streamlit_app.py` (lignes 23-65):

```python
.number-cell {
    background-color: #ffffff;  # Changez ici
    border: 2px solid #4CAF50;
    ...
}
```

### Ajouter des Opérateurs

Modifiez la méthode `_create_valid_block()` pour inclure ×, -, etc.:

```python
# Choisir un opérateur aléatoire
operator = random.choice(['+', '-', '×'])

if operator == '+':
    c = a + b
elif operator == '-':
    c = max(a, b) - min(a, b)  # Éviter les négatifs
else:  # ×
    c = a * b
```

## 🐛 Dépannage

### L'app ne démarre pas

```bash
# Réinstaller Streamlit
pip3 install --upgrade streamlit

# Vérifier la version
streamlit --version
```

### Port déjà utilisé

```bash
# Utiliser un autre port
streamlit run streamlit_app.py --server.port 8502
```

### Erreurs de génération

- Essayez une dimension plus petite (n=5 ou 6)
- Réduisez le nombre maximum
- Régénérez avec le bouton 🎲

## 📊 Exemples d'Utilisation

### Test Rapide
1. Dimension: 5×5
2. Mode normal
3. Cliquez "Générer"
4. Vérifiez que toutes les équations sont valides ✅

### Mode Puzzle
1. Dimension: 10×10
2. Activez "Mode Puzzle"
3. Pourcentage: 30%
4. Décochez "Afficher la solution"
5. Essayez de retrouver les nombres cachés!

### Test de Scalabilité
1. Dimension: 15×15
2. Nombre max: 50
3. Observez le temps de génération (< 1 seconde normalement)

## 🔧 Architecture Technique

### Structure de l'App

```
streamlit_app.py
├── CarreDakarGenerator (Classe)
│   ├── __init__()
│   ├── generate()              # Génération de grille
│   ├── _create_valid_block()   # Création de blocs 5×5
│   ├── hide_numbers()          # Mode puzzle
│   ├── get_cell_type()         # Typage des cellules
│   └── verify_equations()      # Validation
│
├── render_grid()               # Rendu HTML
└── main()                      # Application principale
```

### Flux de Données

```
1. User Input (sidebar)
   ↓
2. CarreDakarGenerator.generate()
   ↓
3. Grid stored in st.session_state
   ↓
4. render_grid() displays HTML
   ↓
5. verify_equations() validates
   ↓
6. Display results
```

## 🚀 Prochaines Étapes

### Améliorations Possibles

1. **Solveur Interactif**
   - Permettre à l'utilisateur de remplir les cases
   - Vérification en temps réel
   - Indices progressifs

2. **Export/Import**
   - Sauvegarder les grilles en JSON
   - Partager des puzzles
   - Importer des grilles personnalisées

3. **Statistiques Avancées**
   - Historique des générations
   - Temps de résolution moyen
   - Graphiques de performance

4. **Modes de Jeu**
   - Contre-la-montre
   - Défi quotidien
   - Mode compétitif

## 📝 Notes Techniques

### Performance

- Génération: O(n²) - très rapide
- Validation: O(n) - linéaire en nombre d'équations
- Rendu: Optimisé avec HTML custom

### Limitations Actuelles

- Validation parfois imprécise si les cellules vides perturbent les équations
- Mode puzzle ne garantit pas encore la solution unique
- Opérateurs limités à + pour l'instant (facile à étendre)

### Solutions

Ces limitations seront résolues dans les prochaines versions:
1. Amélioration de l'algorithme de parsing des équations
2. Vérificateur de solution unique
3. Support de tous les opérateurs (+, -, ×)

## 🎓 Ressources

- **Documentation Streamlit:** https://docs.streamlit.io
- **Théorème d'existence:** Voir `FINAL_ANALYSIS.md`
- **Algorithmes:** Voir `demo_complete.py`

---

**Créé avec:** Python 3.13 + Streamlit 1.31+

**Auteur:** Projet Carré de Dakar

**Licence:** MIT (à définir)
