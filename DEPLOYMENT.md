# 🚀 Déploiement sur Streamlit Cloud

Ce guide vous explique comment déployer l'application Carré de Dakar sur Streamlit Cloud.

## ✅ Prérequis

- [x] Compte GitHub (avec le repo carre_dakar)
- [ ] Compte Streamlit Cloud (gratuit)
- [x] Application fonctionnelle localement

## 📋 Étapes de Déploiement

### 1. Créer un Compte Streamlit Cloud

1. Allez sur https://streamlit.io/cloud
2. Cliquez sur "Sign up"
3. Connectez-vous avec votre compte GitHub (@ArthurSrz)
4. Autorisez Streamlit à accéder à vos repos

### 2. Déployer l'Application

#### Option A: Via l'Interface Web (Recommandé)

1. **Aller sur le Dashboard**
   - https://share.streamlit.io/

2. **Cliquer sur "New app"**

3. **Configurer le déploiement:**
   ```
   Repository: ArthurSrz/carre_dakar
   Branch: main
   Main file path: streamlit_app.py
   ```

4. **Paramètres avancés (optionnel):**
   - Python version: 3.13 (ou 3.11 si 3.13 non disponible)
   - Secrets: (laisser vide pour l'instant)

5. **Cliquer sur "Deploy!"**

   L'application sera disponible à:
   ```
   https://carre-dakar.streamlit.app
   ```
   ou
   ```
   https://arthursrz-carre-dakar-streamlit-app.streamlit.app
   ```

#### Option B: Via streamlit CLI

```bash
# Installer streamlit CLI
pip install streamlit

# Se connecter
streamlit login

# Déployer
streamlit deploy streamlit_app.py
```

### 3. Vérifier le Déploiement

Une fois déployé, vous verrez:
- ✅ Build logs en temps réel
- ✅ URL de l'app
- ✅ Statut du déploiement

**Test initial:**
1. Ouvrir l'URL de l'app
2. Vérifier que la grille s'affiche
3. Tester la génération avec différentes dimensions
4. Activer le mode puzzle

### 4. Configuration Post-Déploiement

#### Ajouter des Secrets (si nécessaire)

Si vous voulez utiliser l'API Aristotle dans l'app:

1. Dans le dashboard Streamlit Cloud
2. Cliquer sur "Settings" → "Secrets"
3. Ajouter:
   ```toml
   ARISTOTLE_API_KEY = "arstl_8uRJkALkH7XKMTD45e1dAc1iuej9oYCAv00Ekd62KSE"
   ```

#### Personnaliser le Domaine (Optionnel)

Streamlit Cloud gratuit fournit: `*.streamlit.app`

Pour un domaine personnalisé (ex: carre-dakar.com):
- Upgrade vers plan payant
- Configurer DNS CNAME

## 🔧 Troubleshooting

### Erreur: "Module not found"

**Solution:** Vérifier `requirements.txt`

```bash
# Localement, vérifier les dépendances
pip freeze > requirements_full.txt
# Comparer avec requirements.txt actuel
```

### Erreur: "App is not loading"

**Solutions:**
1. Vérifier les logs dans le dashboard
2. Tester localement: `streamlit run streamlit_app.py`
3. Vérifier que le fichier est bien `streamlit_app.py`

### L'app est lente

**Optimisations:**
1. Utiliser `@st.cache_data` pour les fonctions lourdes
2. Réduire la taille de la grille par défaut
3. Optimiser les imports

### Erreur de mémoire

Streamlit Cloud gratuit a des limites:
- RAM: 1 GB
- CPU: Partagé

**Solutions:**
- Limiter la dimension max à 12×12
- Upgrade vers plan payant si besoin

## 📊 Monitoring

### Analytics

Streamlit Cloud fournit:
- Nombre de visiteurs
- Sessions actives
- Erreurs en production

**Accès:** Dashboard → App → Analytics

### Logs

Voir les logs en temps réel:
1. Dashboard → App
2. Onglet "Logs"
3. Filter par niveau (Info, Warning, Error)

## 🔄 Mises à Jour

### Déploiement Automatique

Par défaut, chaque push sur `main` redéploie automatiquement!

```bash
# Faire des changements
git add streamlit_app.py
git commit -m "Improve: Add multiplication operator support"
git push origin main

# L'app se redéploie automatiquement! 🚀
```

### Déploiement Manuel

Dans le dashboard:
1. Cliquer sur "Reboot app"
2. Ou changer de branche

## 🎨 Personnalisation

### Thème Personnalisé

Déjà configuré dans `.streamlit/config.toml`:
```toml
[theme]
primaryColor = "#4CAF50"
backgroundColor = "#f0f2f6"
secondaryBackgroundColor = "#ffffff"
textColor = "#1e1e1e"
```

### Favicon et Titre

Ajouter dans `streamlit_app.py`:
```python
st.set_page_config(
    page_title="Carré de Dakar",
    page_icon="🎯",
    layout="wide"
)
```

Déjà fait! ✅

## 🔒 Sécurité

### Secrets Management

**À FAIRE:**
- ✅ Ne JAMAIS committer `.streamlit/secrets.toml`
- ✅ Ajouter secrets via dashboard Streamlit
- ✅ Utiliser `st.secrets["KEY"]` dans le code

### Rate Limiting

Streamlit Cloud a des limites:
- Gratuit: Illimité pour usage personnel
- Payant: Pour production

## 💰 Coûts

### Plan Gratuit (Community)
- ✅ Illimité pour projets publics
- ✅ 1 GB RAM
- ✅ Déploiements illimités
- ❌ Pas de domaine custom
- ❌ Pas de support prioritaire

### Plan Payant (à partir de $20/mois)
- ✅ Plus de ressources
- ✅ Domaine custom
- ✅ Support prioritaire
- ✅ Analytics avancés

**Pour ce projet:** Plan gratuit suffit largement! 🎉

## 📱 Partage

Une fois déployé, partagez:

### Badge pour README

Ajoutez dans `README.md`:
```markdown
[![Streamlit App](https://static.streamlit.io/badges/streamlit_badge_black_white.svg)](https://carre-dakar.streamlit.app)
```

### QR Code

Générez un QR code pointant vers votre app:
- https://www.qr-code-generator.com/

### Social Media

```markdown
🎯 Essayez le Carré de Dakar en ligne!

Application interactive pour générer et résoudre des grilles
mathématiques où toutes les équations sont valides.

🔗 https://carre-dakar.streamlit.app

#Streamlit #Python #Mathematics
```

## 🎯 Checklist de Déploiement

Avant de déployer:

- [x] Code testé localement
- [x] requirements.txt à jour
- [x] .gitignore configuré
- [x] .streamlit/config.toml créé
- [x] README.md avec lien vers l'app
- [ ] Compte Streamlit Cloud créé
- [ ] App déployée
- [ ] URL testée
- [ ] README mis à jour avec badge

Après déploiement:

- [ ] Tester toutes les fonctionnalités
- [ ] Vérifier les logs
- [ ] Partager sur les réseaux sociaux
- [ ] Ajouter l'URL au README GitHub

## 🚀 Résultat Final

Votre app sera accessible 24/7 à:
```
https://[votre-app].streamlit.app
```

Avec:
- ✅ HTTPS automatique
- ✅ Mises à jour automatiques
- ✅ Monitoring inclus
- ✅ Hébergement gratuit
- ✅ Zero configuration

## 📞 Support

**Problèmes?**
- Documentation: https://docs.streamlit.io/streamlit-community-cloud
- Forum: https://discuss.streamlit.io/
- GitHub Issues: https://github.com/ArthurSrz/carre_dakar/issues

---

**Créé le:** 2026-02-01
**Auteur:** Arthur Sarazin
**App:** Carré de Dakar
